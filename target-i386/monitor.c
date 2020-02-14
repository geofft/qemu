/*
 * QEMU monitor
 *
 * Copyright (c) 2003-2004 Fabrice Bellard
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
#include "cpu.h"
#include "monitor/monitor.h"
#include "monitor/hmp-target.h"
#include "hw/i386/pc.h"
#include "sysemu/kvm.h"
#include "hmp.h"


/**
 * PTLayout describes the layout of an x86 page table in enough detail
 * to fully decode up to a 4-level 64-bit page table tree.
 */
typedef struct PTLayout {
    int levels, entsize;
    int entries[4];             /* Entries in each table level */
    int shift[4];               /* VA bit shift each each level */
    bool pse[4];                /* Whether PSE bit is valid */
    const char *names[4];
    int vaw, paw;               /* VA and PA width in characters */
} PTLayout;

/**
 * PTIter provides a generic way to traverse and decode an x86 page
 * table tree.
 */
typedef struct PTIter {
    const PTLayout *layout;
    bool pse;                   /* PSE enabled */
    int level;                  /* Current level */
    int i[4];                   /* Index at each level */
    hwaddr base[4];             /* Physical base pointer */

    uint64_t ent;               /* Current entry */
    bool present, leaf;
    target_ulong va;
    hwaddr pa;
    target_ulong  size;
} PTIter;

static bool ptiter_succ(PTIter *it);

/**
 * Initialize a PTIter to point to the first entry of the page table's
 * top level.  On failure, prints a message to mon and returns false.
 */
static bool ptiter_init(Monitor *mon, PTIter *it)
{
    static const PTLayout l32 = {
        2, 4, {1024, 1024}, {22, 12}, {1, 0}, {"PDE", "PTE"}, 8, 8
    };
    static const PTLayout lpae = {
        3, 8, {4, 512, 512}, {30, 21, 12}, {0, 1, 0},
        {"PDP", "PDE", "PTE"}, 8, 13
    };
#ifdef TARGET_X86_64
    static const PTLayout l64 = {
        4, 8, {512, 512, 512, 512}, {39, 30, 21, 12}, {0, 1, 1, 0},
        {"PML4", "PDP", "PDE", "PTE"}, 12, 13
    };
#endif
    CPUArchState *env;

    env = mon_get_cpu_env();

    if (!(env->cr[0] & CR0_PG_MASK)) {
        monitor_printf(mon, "PG disabled\n");
        return false;
    }

    memset(it, 0, sizeof(*it));
    if (env->cr[4] & CR4_PAE_MASK) {
#ifdef TARGET_X86_64
        if (env->hflags & HF_LMA_MASK) {
            it->layout = &l64;
            it->base[0] = env->cr[3] & 0x3fffffffff000ULL;
        } else
#endif
        {
            it->layout = &lpae;
            it->base[0] = env->cr[3] & ~0x1f;
        }
        it->pse = true;
    } else {
        it->layout = &l32;
        it->base[0] = env->cr[3] & ~0xfff;
        it->pse = (env->cr[4] & CR4_PSE_MASK);
    }

    /* Trick ptiter_succ into doing the hard initialization. */
    it->i[0] = -1;
    it->leaf = true;
    ptiter_succ(it);
    return true;
}

/**
 * Move a PTIter to the successor of the current entry.  Specifically:
 * if the iterator points to a leaf, move to its next sibling, or to
 * the next sibling of a parent if it has no more siblings.  If the
 * iterator points to a non-leaf, move to its first child.  If there
 * is no successor, return false.
 *
 * Note that the resulting entry may not be marked present, though
 * non-present entries are always leafs (within a page
 * table/directory/etc, this will always visit all entries).
 */
static bool ptiter_succ(PTIter *it)
{
    int i, l, entsize;
    uint64_t ent64;
    uint32_t ent32;
    bool large;

    if (it->level < 0) {
        return false;
    } else if (!it->leaf) {
        /* Move to this entry's first child */
        it->level++;
        it->base[it->level] = it->pa;
        it->i[it->level] = 0;
    } else {
        /* Move forward and, if we hit the end of this level, up */
        while (++it->i[it->level] == it->layout->entries[it->level]) {
            if (it->level-- == 0) {
                /* We're out of page table */
                return false;
            }
        }
    }

    /* Read this entry */
    l = it->level;
    entsize = it->layout->entsize;
    cpu_physical_memory_read(it->base[l] + it->i[l] * entsize,
                             entsize == 4 ? (void *)&ent32 : (void *)&ent64,
                             entsize);
    if (entsize == 4) {
        it->ent = le32_to_cpu(ent32);
    } else {
        it->ent = le64_to_cpu(ent64);
    }

    /* Decode the entry */
    large = (it->pse && it->layout->pse[l] && (it->ent & PG_PSE_MASK));
    it->present = it->ent & PG_PRESENT_MASK;
    it->leaf = (large || !it->present || (l+1 == it->layout->levels));
    it->va = 0;
    for (i = 0; i <= l; i++) {
        it->va |= (uint64_t)it->i[i] << it->layout->shift[i];
    }
    it->pa = it->ent & (large ? 0x3ffffffffc000ULL : 0x3fffffffff000ULL);
    it->size = 1 << it->layout->shift[l];
    return true;
}

/* Return true if the page tree rooted at iter is complete and
 * compatible with compat.  last will be filled with the last entry at
 * each level.  If false, does not change iter and last can be filled
 * with anything; if true, returns with iter at the next entry on the
 * same level, or the next parent entry if iter is on the last entry
 * of this level. */
static bool pg_complete(PTIter *root, const PTIter compat[], PTIter last[])
{
    PTIter iter = *root;

    if ((root->ent & 0xfff) != (compat[root->level].ent & 0xfff)) {
        return false;
    }

    last[root->level] = *root;
    ptiter_succ(&iter);
    if (!root->leaf) {
        /* Are all of the direct children of root complete? */
        while (iter.level == root->level + 1) {
            if (!pg_complete(&iter, compat, last)) {
                return false;
            }
        }
    }
    assert(iter.level <= root->level);
    assert(iter.level == root->level ?
           iter.i[iter.level] == root->i[iter.level] + 1 : 1);
    *root = iter;
    return true;
}

static char *pg_bits(uint64_t ent)
{
    static char buf[32];
    sprintf(buf, "%c%c%c%c%c%c%c%c%c%c",
            /* TODO: Some of these change depending on level */
            ent & PG_NX_MASK ? 'X' : '-',
            ent & PG_GLOBAL_MASK ? 'G' : '-',
            ent & PG_PSE_MASK ? 'S' : '-',
            ent & PG_DIRTY_MASK ? 'D' : '-',
            ent & PG_ACCESSED_MASK ? 'A' : '-',
            ent & PG_PCD_MASK ? 'C' : '-',
            ent & PG_PWT_MASK ? 'T' : '-',
            ent & PG_USER_MASK ? 'U' : '-',
            ent & PG_RW_MASK ? 'W' : '-',
            ent & PG_PRESENT_MASK ? 'P' : '-');
    return buf;
}

static void pg_print(Monitor *mon, PTIter *s, PTIter *l)
{
    int lev = s->level;
    char buf[128];
    char *pos = buf, *end = buf + sizeof(buf);

    /* VFN range */
    pos += sprintf(pos, "%*s[%0*"PRIx64"-%0*"PRIx64"] ",
                   lev*2, "",
                   s->layout->vaw - 3, (uint64_t)s->va >> 12,
                   s->layout->vaw - 3, ((uint64_t)l->va + l->size - 1) >> 12);

    /* Slot */
    if (s->i[lev] == l->i[lev]) {
        pos += sprintf(pos, "%4s[%03x]    ",
                       s->layout->names[lev], s->i[lev]);
    } else {
        pos += sprintf(pos, "%4s[%03x-%03x]",
                       s->layout->names[lev], s->i[lev], l->i[lev]);
    }

    /* Flags */
    pos += sprintf(pos, " %s", pg_bits(s->ent));

    /* Range-compressed PFN's */
    if (s->leaf) {
        PTIter iter = *s;
        int i = 0;
        bool exhausted = false;
        while (!exhausted && i++ < 10) {
            hwaddr pas = iter.pa, pae = iter.pa + iter.size;
            while (ptiter_succ(&iter) && iter.va <= l->va) {
                if (iter.level == s->level) {
                    if (iter.pa == pae) {
                        pae = iter.pa + iter.size;
                    } else {
                        goto print;
                    }
                }
            }
            exhausted = true;

print:
            if (pas >> 12 == (pae - 1) >> 12) {
                pos += snprintf(pos, end-pos, " %0*"PRIx64,
                                s->layout->paw - 3, (uint64_t)pas >> 12);
            } else {
                pos += snprintf(pos, end-pos, " %0*"PRIx64"-%0*"PRIx64,
                                s->layout->paw - 3, (uint64_t)pas >> 12,
                                s->layout->paw - 3, (uint64_t)(pae - 1) >> 12);
            }
            pos = MIN(pos, end);
        }
    }

    /* Trim line to fit screen */
    if (pos - buf > 79) {
        strcpy(buf + 77, "..");
    }

    monitor_printf(mon, "%s\n", buf);
}

void pg_info(Monitor *mon, const QDict *qdict)
{
    PTIter iter;

    if (!ptiter_init(mon, &iter)) {
        return;
    }

    /* Header line */
    monitor_printf(mon, "%-*s %-13s %-10s %*s%s\n",
                   3 + 2 * (iter.layout->vaw-3), "VPN range",
                   "Entry", "Flags",
                   2*(iter.layout->levels-1), "", "Physical page");

    while (iter.level >= 0) {
        int i, startLevel, maxLevel;
        PTIter start[4], last[4], nlast[4];
        bool compressed = false;

        /* Skip to the next present entry */
        do { } while (!iter.present && ptiter_succ(&iter));
        if (iter.level < 0) {
            break;
        }

        /* Find a run of complete entries starting at iter and staying
         * on the same level. */
        startLevel = iter.level;
        memset(start, 0, sizeof(start));
        do {
            start[iter.level] = iter;
        } while (!iter.leaf && ptiter_succ(&iter));
        maxLevel = iter.level;
        iter = start[startLevel];
        while (iter.level == startLevel && pg_complete(&iter, start, nlast)) {
            compressed = true;
            memcpy(last, nlast, sizeof(last));
        }

        if (compressed) {
            /* We found a run we can show as a range spanning
             * [startLevel, maxLevel].  start stores the first entry
             * at each level and last stores the last entry. */
            for (i = startLevel; i <= maxLevel; i++) {
                pg_print(mon, &start[i], &last[i]);
            }
        } else {
            /* No luck finding a range.  Iter hasn't moved. */
            pg_print(mon, &iter, &iter);
            ptiter_succ(&iter);
        }
    }
}

static void print_pte(Monitor *mon, hwaddr addr,
                      hwaddr pte,
                      hwaddr mask)
{
#ifdef TARGET_X86_64
    if (addr & (1ULL << 47)) {
        addr |= -1LL << 48;
    }
#endif
    monitor_printf(mon, TARGET_FMT_plx ": " TARGET_FMT_plx
                   " %c%c%c%c%c%c%c%c%c\n",
                   addr,
                   pte & mask,
                   pte & PG_NX_MASK ? 'X' : '-',
                   pte & PG_GLOBAL_MASK ? 'G' : '-',
                   pte & PG_PSE_MASK ? 'P' : '-',
                   pte & PG_DIRTY_MASK ? 'D' : '-',
                   pte & PG_ACCESSED_MASK ? 'A' : '-',
                   pte & PG_PCD_MASK ? 'C' : '-',
                   pte & PG_PWT_MASK ? 'T' : '-',
                   pte & PG_USER_MASK ? 'U' : '-',
                   pte & PG_RW_MASK ? 'W' : '-');
}

static void tlb_info_32(Monitor *mon, CPUArchState *env)
{
    unsigned int l1, l2;
    uint32_t pgd, pde, pte;

    pgd = env->cr[3] & ~0xfff;
    for(l1 = 0; l1 < 1024; l1++) {
        cpu_physical_memory_read(pgd + l1 * 4, &pde, 4);
        pde = le32_to_cpu(pde);
        if (pde & PG_PRESENT_MASK) {
            if ((pde & PG_PSE_MASK) && (env->cr[4] & CR4_PSE_MASK)) {
                /* 4M pages */
                print_pte(mon, (l1 << 22), pde, ~((1 << 21) - 1));
            } else {
                for(l2 = 0; l2 < 1024; l2++) {
                    cpu_physical_memory_read((pde & ~0xfff) + l2 * 4, &pte, 4);
                    pte = le32_to_cpu(pte);
                    if (pte & PG_PRESENT_MASK) {
                        print_pte(mon, (l1 << 22) + (l2 << 12),
                                  pte & ~PG_PSE_MASK,
                                  ~0xfff);
                    }
                }
            }
        }
    }
}

static void tlb_info_pae32(Monitor *mon, CPUArchState *env)
{
    unsigned int l1, l2, l3;
    uint64_t pdpe, pde, pte;
    uint64_t pdp_addr, pd_addr, pt_addr;

    pdp_addr = env->cr[3] & ~0x1f;
    for (l1 = 0; l1 < 4; l1++) {
        cpu_physical_memory_read(pdp_addr + l1 * 8, &pdpe, 8);
        pdpe = le64_to_cpu(pdpe);
        if (pdpe & PG_PRESENT_MASK) {
            pd_addr = pdpe & 0x3fffffffff000ULL;
            for (l2 = 0; l2 < 512; l2++) {
                cpu_physical_memory_read(pd_addr + l2 * 8, &pde, 8);
                pde = le64_to_cpu(pde);
                if (pde & PG_PRESENT_MASK) {
                    if (pde & PG_PSE_MASK) {
                        /* 2M pages with PAE, CR4.PSE is ignored */
                        print_pte(mon, (l1 << 30 ) + (l2 << 21), pde,
                                  ~((hwaddr)(1 << 20) - 1));
                    } else {
                        pt_addr = pde & 0x3fffffffff000ULL;
                        for (l3 = 0; l3 < 512; l3++) {
                            cpu_physical_memory_read(pt_addr + l3 * 8, &pte, 8);
                            pte = le64_to_cpu(pte);
                            if (pte & PG_PRESENT_MASK) {
                                print_pte(mon, (l1 << 30 ) + (l2 << 21)
                                          + (l3 << 12),
                                          pte & ~PG_PSE_MASK,
                                          ~(hwaddr)0xfff);
                            }
                        }
                    }
                }
            }
        }
    }
}

#ifdef TARGET_X86_64
static void tlb_info_64(Monitor *mon, CPUArchState *env)
{
    uint64_t l1, l2, l3, l4;
    uint64_t pml4e, pdpe, pde, pte;
    uint64_t pml4_addr, pdp_addr, pd_addr, pt_addr;

    pml4_addr = env->cr[3] & 0x3fffffffff000ULL;
    for (l1 = 0; l1 < 512; l1++) {
        cpu_physical_memory_read(pml4_addr + l1 * 8, &pml4e, 8);
        pml4e = le64_to_cpu(pml4e);
        if (pml4e & PG_PRESENT_MASK) {
            pdp_addr = pml4e & 0x3fffffffff000ULL;
            for (l2 = 0; l2 < 512; l2++) {
                cpu_physical_memory_read(pdp_addr + l2 * 8, &pdpe, 8);
                pdpe = le64_to_cpu(pdpe);
                if (pdpe & PG_PRESENT_MASK) {
                    if (pdpe & PG_PSE_MASK) {
                        /* 1G pages, CR4.PSE is ignored */
                        print_pte(mon, (l1 << 39) + (l2 << 30), pdpe,
                                  0x3ffffc0000000ULL);
                    } else {
                        pd_addr = pdpe & 0x3fffffffff000ULL;
                        for (l3 = 0; l3 < 512; l3++) {
                            cpu_physical_memory_read(pd_addr + l3 * 8, &pde, 8);
                            pde = le64_to_cpu(pde);
                            if (pde & PG_PRESENT_MASK) {
                                if (pde & PG_PSE_MASK) {
                                    /* 2M pages, CR4.PSE is ignored */
                                    print_pte(mon, (l1 << 39) + (l2 << 30) +
                                              (l3 << 21), pde,
                                              0x3ffffffe00000ULL);
                                } else {
                                    pt_addr = pde & 0x3fffffffff000ULL;
                                    for (l4 = 0; l4 < 512; l4++) {
                                        cpu_physical_memory_read(pt_addr
                                                                 + l4 * 8,
                                                                 &pte, 8);
                                        pte = le64_to_cpu(pte);
                                        if (pte & PG_PRESENT_MASK) {
                                            print_pte(mon, (l1 << 39) +
                                                      (l2 << 30) +
                                                      (l3 << 21) + (l4 << 12),
                                                      pte & ~PG_PSE_MASK,
                                                      0x3fffffffff000ULL);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
#endif /* TARGET_X86_64 */

void hmp_info_tlb(Monitor *mon, const QDict *qdict)
{
    CPUArchState *env;

    env = mon_get_cpu_env();

    if (!(env->cr[0] & CR0_PG_MASK)) {
        monitor_printf(mon, "PG disabled\n");
        return;
    }
    if (env->cr[4] & CR4_PAE_MASK) {
#ifdef TARGET_X86_64
        if (env->hflags & HF_LMA_MASK) {
            tlb_info_64(mon, env);
        } else
#endif
        {
            tlb_info_pae32(mon, env);
        }
    } else {
        tlb_info_32(mon, env);
    }
}

static void mem_print(Monitor *mon, hwaddr *pstart,
                      int *plast_prot,
                      hwaddr end, int prot)
{
    int prot1;
    prot1 = *plast_prot;
    if (prot != prot1) {
        if (*pstart != -1) {
            monitor_printf(mon, TARGET_FMT_plx "-" TARGET_FMT_plx " "
                           TARGET_FMT_plx " %c%c%c\n",
                           *pstart, end, end - *pstart,
                           prot1 & PG_USER_MASK ? 'u' : '-',
                           'r',
                           prot1 & PG_RW_MASK ? 'w' : '-');
        }
        if (prot != 0)
            *pstart = end;
        else
            *pstart = -1;
        *plast_prot = prot;
    }
}

static void mem_info_32(Monitor *mon, CPUArchState *env)
{
    unsigned int l1, l2;
    int prot, last_prot;
    uint32_t pgd, pde, pte;
    hwaddr start, end;

    pgd = env->cr[3] & ~0xfff;
    last_prot = 0;
    start = -1;
    for(l1 = 0; l1 < 1024; l1++) {
        cpu_physical_memory_read(pgd + l1 * 4, &pde, 4);
        pde = le32_to_cpu(pde);
        end = l1 << 22;
        if (pde & PG_PRESENT_MASK) {
            if ((pde & PG_PSE_MASK) && (env->cr[4] & CR4_PSE_MASK)) {
                prot = pde & (PG_USER_MASK | PG_RW_MASK | PG_PRESENT_MASK);
                mem_print(mon, &start, &last_prot, end, prot);
            } else {
                for(l2 = 0; l2 < 1024; l2++) {
                    cpu_physical_memory_read((pde & ~0xfff) + l2 * 4, &pte, 4);
                    pte = le32_to_cpu(pte);
                    end = (l1 << 22) + (l2 << 12);
                    if (pte & PG_PRESENT_MASK) {
                        prot = pte & pde &
                            (PG_USER_MASK | PG_RW_MASK | PG_PRESENT_MASK);
                    } else {
                        prot = 0;
                    }
                    mem_print(mon, &start, &last_prot, end, prot);
                }
            }
        } else {
            prot = 0;
            mem_print(mon, &start, &last_prot, end, prot);
        }
    }
    /* Flush last range */
    mem_print(mon, &start, &last_prot, (hwaddr)1 << 32, 0);
}

static void mem_info_pae32(Monitor *mon, CPUArchState *env)
{
    unsigned int l1, l2, l3;
    int prot, last_prot;
    uint64_t pdpe, pde, pte;
    uint64_t pdp_addr, pd_addr, pt_addr;
    hwaddr start, end;

    pdp_addr = env->cr[3] & ~0x1f;
    last_prot = 0;
    start = -1;
    for (l1 = 0; l1 < 4; l1++) {
        cpu_physical_memory_read(pdp_addr + l1 * 8, &pdpe, 8);
        pdpe = le64_to_cpu(pdpe);
        end = l1 << 30;
        if (pdpe & PG_PRESENT_MASK) {
            pd_addr = pdpe & 0x3fffffffff000ULL;
            for (l2 = 0; l2 < 512; l2++) {
                cpu_physical_memory_read(pd_addr + l2 * 8, &pde, 8);
                pde = le64_to_cpu(pde);
                end = (l1 << 30) + (l2 << 21);
                if (pde & PG_PRESENT_MASK) {
                    if (pde & PG_PSE_MASK) {
                        prot = pde & (PG_USER_MASK | PG_RW_MASK |
                                      PG_PRESENT_MASK);
                        mem_print(mon, &start, &last_prot, end, prot);
                    } else {
                        pt_addr = pde & 0x3fffffffff000ULL;
                        for (l3 = 0; l3 < 512; l3++) {
                            cpu_physical_memory_read(pt_addr + l3 * 8, &pte, 8);
                            pte = le64_to_cpu(pte);
                            end = (l1 << 30) + (l2 << 21) + (l3 << 12);
                            if (pte & PG_PRESENT_MASK) {
                                prot = pte & pde & (PG_USER_MASK | PG_RW_MASK |
                                                    PG_PRESENT_MASK);
                            } else {
                                prot = 0;
                            }
                            mem_print(mon, &start, &last_prot, end, prot);
                        }
                    }
                } else {
                    prot = 0;
                    mem_print(mon, &start, &last_prot, end, prot);
                }
            }
        } else {
            prot = 0;
            mem_print(mon, &start, &last_prot, end, prot);
        }
    }
    /* Flush last range */
    mem_print(mon, &start, &last_prot, (hwaddr)1 << 32, 0);
}


#ifdef TARGET_X86_64
static void mem_info_64(Monitor *mon, CPUArchState *env)
{
    int prot, last_prot;
    uint64_t l1, l2, l3, l4;
    uint64_t pml4e, pdpe, pde, pte;
    uint64_t pml4_addr, pdp_addr, pd_addr, pt_addr, start, end;

    pml4_addr = env->cr[3] & 0x3fffffffff000ULL;
    last_prot = 0;
    start = -1;
    for (l1 = 0; l1 < 512; l1++) {
        cpu_physical_memory_read(pml4_addr + l1 * 8, &pml4e, 8);
        pml4e = le64_to_cpu(pml4e);
        end = l1 << 39;
        if (pml4e & PG_PRESENT_MASK) {
            pdp_addr = pml4e & 0x3fffffffff000ULL;
            for (l2 = 0; l2 < 512; l2++) {
                cpu_physical_memory_read(pdp_addr + l2 * 8, &pdpe, 8);
                pdpe = le64_to_cpu(pdpe);
                end = (l1 << 39) + (l2 << 30);
                if (pdpe & PG_PRESENT_MASK) {
                    if (pdpe & PG_PSE_MASK) {
                        prot = pdpe & (PG_USER_MASK | PG_RW_MASK |
                                       PG_PRESENT_MASK);
                        prot &= pml4e;
                        mem_print(mon, &start, &last_prot, end, prot);
                    } else {
                        pd_addr = pdpe & 0x3fffffffff000ULL;
                        for (l3 = 0; l3 < 512; l3++) {
                            cpu_physical_memory_read(pd_addr + l3 * 8, &pde, 8);
                            pde = le64_to_cpu(pde);
                            end = (l1 << 39) + (l2 << 30) + (l3 << 21);
                            if (pde & PG_PRESENT_MASK) {
                                if (pde & PG_PSE_MASK) {
                                    prot = pde & (PG_USER_MASK | PG_RW_MASK |
                                                  PG_PRESENT_MASK);
                                    prot &= pml4e & pdpe;
                                    mem_print(mon, &start, &last_prot, end, prot);
                                } else {
                                    pt_addr = pde & 0x3fffffffff000ULL;
                                    for (l4 = 0; l4 < 512; l4++) {
                                        cpu_physical_memory_read(pt_addr
                                                                 + l4 * 8,
                                                                 &pte, 8);
                                        pte = le64_to_cpu(pte);
                                        end = (l1 << 39) + (l2 << 30) +
                                            (l3 << 21) + (l4 << 12);
                                        if (pte & PG_PRESENT_MASK) {
                                            prot = pte & (PG_USER_MASK | PG_RW_MASK |
                                                          PG_PRESENT_MASK);
                                            prot &= pml4e & pdpe & pde;
                                        } else {
                                            prot = 0;
                                        }
                                        mem_print(mon, &start, &last_prot, end, prot);
                                    }
                                }
                            } else {
                                prot = 0;
                                mem_print(mon, &start, &last_prot, end, prot);
                            }
                        }
                    }
                } else {
                    prot = 0;
                    mem_print(mon, &start, &last_prot, end, prot);
                }
            }
        } else {
            prot = 0;
            mem_print(mon, &start, &last_prot, end, prot);
        }
    }
    /* Flush last range */
    mem_print(mon, &start, &last_prot, (hwaddr)1 << 48, 0);
}
#endif /* TARGET_X86_64 */

void hmp_info_mem(Monitor *mon, const QDict *qdict)
{
    CPUArchState *env;

    env = mon_get_cpu_env();

    if (!(env->cr[0] & CR0_PG_MASK)) {
        monitor_printf(mon, "PG disabled\n");
        return;
    }
    if (env->cr[4] & CR4_PAE_MASK) {
#ifdef TARGET_X86_64
        if (env->hflags & HF_LMA_MASK) {
            mem_info_64(mon, env);
        } else
#endif
        {
            mem_info_pae32(mon, env);
        }
    } else {
        mem_info_32(mon, env);
    }
}

void hmp_mce(Monitor *mon, const QDict *qdict)
{
    X86CPU *cpu;
    CPUState *cs;
    int cpu_index = qdict_get_int(qdict, "cpu_index");
    int bank = qdict_get_int(qdict, "bank");
    uint64_t status = qdict_get_int(qdict, "status");
    uint64_t mcg_status = qdict_get_int(qdict, "mcg_status");
    uint64_t addr = qdict_get_int(qdict, "addr");
    uint64_t misc = qdict_get_int(qdict, "misc");
    int flags = MCE_INJECT_UNCOND_AO;

    if (qdict_get_try_bool(qdict, "broadcast", false)) {
        flags |= MCE_INJECT_BROADCAST;
    }
    cs = qemu_get_cpu(cpu_index);
    if (cs != NULL) {
        cpu = X86_CPU(cs);
        cpu_x86_inject_mce(mon, cpu, bank, status, mcg_status, addr, misc,
                           flags);
    }
}

static target_long monitor_get_pc(const struct MonitorDef *md, int val)
{
    CPUArchState *env = mon_get_cpu_env();
    return env->eip + env->segs[R_CS].base;
}

const MonitorDef monitor_defs[] = {
#define SEG(name, seg) \
    { name, offsetof(CPUX86State, segs[seg].selector), NULL, MD_I32 },\
    { name ".base", offsetof(CPUX86State, segs[seg].base) },\
    { name ".limit", offsetof(CPUX86State, segs[seg].limit), NULL, MD_I32 },

    { "eax", offsetof(CPUX86State, regs[0]) },
    { "ecx", offsetof(CPUX86State, regs[1]) },
    { "edx", offsetof(CPUX86State, regs[2]) },
    { "ebx", offsetof(CPUX86State, regs[3]) },
    { "esp|sp", offsetof(CPUX86State, regs[4]) },
    { "ebp|fp", offsetof(CPUX86State, regs[5]) },
    { "esi", offsetof(CPUX86State, regs[6]) },
    { "edi", offsetof(CPUX86State, regs[7]) },
#ifdef TARGET_X86_64
    { "r8", offsetof(CPUX86State, regs[8]) },
    { "r9", offsetof(CPUX86State, regs[9]) },
    { "r10", offsetof(CPUX86State, regs[10]) },
    { "r11", offsetof(CPUX86State, regs[11]) },
    { "r12", offsetof(CPUX86State, regs[12]) },
    { "r13", offsetof(CPUX86State, regs[13]) },
    { "r14", offsetof(CPUX86State, regs[14]) },
    { "r15", offsetof(CPUX86State, regs[15]) },
#endif
    { "eflags", offsetof(CPUX86State, eflags) },
    { "eip", offsetof(CPUX86State, eip) },
    SEG("cs", R_CS)
    SEG("ds", R_DS)
    SEG("es", R_ES)
    SEG("ss", R_SS)
    SEG("fs", R_FS)
    SEG("gs", R_GS)
    { "pc", 0, monitor_get_pc, },
    { NULL },
};

const MonitorDef *target_monitor_defs(void)
{
    return monitor_defs;
}

void hmp_info_local_apic(Monitor *mon, const QDict *qdict)
{
    x86_cpu_dump_local_apic_state(mon_get_cpu(), (FILE *)mon, monitor_fprintf,
                                  CPU_DUMP_FPU);
}

void hmp_info_io_apic(Monitor *mon, const QDict *qdict)
{
    if (kvm_irqchip_in_kernel()) {
        kvm_ioapic_dump_state(mon, qdict);
    } else {
        ioapic_dump_state(mon, qdict);
    }
}
