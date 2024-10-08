
/*--------------------------------------------------------------------*/
/*--- Cache simulation                                    cg_sim.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Cachegrind, a high-precision tracing profiler
   built with Valgrind.

   Copyright (C) 2002-2017 Nicholas Nethercote
      njn@valgrind.org

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, see <http://www.gnu.org/licenses/>.

   The GNU General Public License is contained in the file COPYING.
*/

/* Notes:
  - simulates a write-allocate cache
  - (block --> set) hash function uses simple bit selection
  - handling of references straddling two cache blocks:
      - counts as only one cache access (not two)
      - both blocks hit                  --> one hit
      - one block hits, the other misses --> one miss
      - both blocks miss                 --> one miss (not two)
*/

/*------------------------------------------------------------*/
/*--- Types and Data Structures                            ---*/
/*------------------------------------------------------------*/
#define DEFAULT_WORD_SIZE     8
#define MAX_NUM_BINS          8

typedef
   struct {
      ULong a;  /* total # memory accesses of this kind */
      ULong m1; /* misses in the first level cache */
      ULong mL; /* misses in the second level cache */
   }
   CacheCC;

typedef
   struct {
      ULong b;  /* total # branches of this kind */
      ULong mp; /* number of branches mispredicted */
   }
   BranchCC;

//------------------------------------------------------------
// Primary data structure #1: CC table
// - Holds the per-source-line hit/miss stats, grouped by file/function/line.
// - an ordered set of CCs.  CC indexing done by file/function/line (as
//   determined from the instrAddr).
// - Traversed for dumping stats at end in file/func/line hierarchy.

typedef struct {
   HChar* file;
   const HChar* fn;
   Int    line;
}
CodeLoc;

typedef struct {
   CodeLoc  loc; /* Source location that these counts pertain to */
   CacheCC  Ir;  /* Insn read counts */
   CacheCC  Dr;  /* Data read counts */
   CacheCC  Dw;  /* Data write/modify counts */
   BranchCC Bc;  /* Conditional branch counts */
   BranchCC Bi;  /* Indirect branch counts */

/*----------Extension of cache efficiency -----------*/
   ULong num_evicts_D1[MAX_NUM_BINS]; /* The number of cachline evictions with n(1~8) words used*/
   ULong num_evicts_LL[MAX_NUM_BINS]; /* The number of cachline evictions with n(1~8) words used*/
} LineCC;

// First compare file, then fn, then line.
static Word cmp_CodeLoc_LineCC(const void *vloc, const void *vcc)
{
   Word res;
   const CodeLoc* a = (const CodeLoc*)vloc;
   const CodeLoc* b = &(((const LineCC*)vcc)->loc);

   res = VG_(strcmp)(a->file, b->file);
   if (0 != res)
      return res;

   res = VG_(strcmp)(a->fn, b->fn);
   if (0 != res)
      return res;

   return a->line - b->line;
}

/*----------Extension of cache efficiency by JinChao-----------*/
Int CU_DEBUG = 0;
VgFile  *cu_fp = NULL;

//Setting nth bit in a bitvector on.
static
void bitop_set(UChar* bv, UInt pos)
{
	if(bv == NULL || pos < 0)
		return;

	*bv |= 1 << pos;	
}

//Setting multiple bits in a bitvector on.
__attribute__((always_inline))
static __inline__
void bitop_set_range(UInt* bv, UInt begin, UInt end)
{
	Int i;
	for(i = begin; i <= end; i++)
		*bv |= 1 << i;
}

// Counting non-zero bits in a bit vector using Brian Kernighan’s Algorithm
__attribute__((always_inline))
static __inline__
UInt bitop_count(UChar bv)
{
	UInt count = 0;

	while(bv) {
		bv &= (bv - 1);
		count ++;
	}

	return count;
}

static
Int open_cu_log(void)
{
   const HChar* cu_out_file = "causage.dbg";
//      VG_(expand_file_name)("--cachegrind-out-file", clo_ce_out_file);

   cu_fp = VG_(fopen)(cu_out_file, VKI_O_CREAT|VKI_O_TRUNC|VKI_O_WRONLY,
                                        VKI_S_IRUSR|VKI_S_IWUSR);
   if (cu_fp == NULL) 
      return -1;

   return 0;
}

static
void close_cu_log(void)
{
   if (!cu_fp) 
      return;

   VG_(fclose)(cu_fp);
}

typedef struct {
  UWord        tag;
  UInt         bitvector;   // keep track of word usage
  Int          line_num; // source code line number
  LineCC       *src_line;   // pointer to LineCC in cg_main.c
} cacheline_t;

typedef struct {
   Int          size;                   /* bytes */
   Int          assoc;
   Int          line_size;              /* bytes */
   Int          sets;
   Int          sets_min_1;
   Int          line_size_bits;
   Int          tag_shift;
   HChar        desc_line[128];         /* large enough */
//   UWord*       tags;
   UInt         line_mask;
   Int          num_words_per_line;
   Int          num_words_bits;
   cacheline_t  *cachelines;
   UInt         *lru_list;
} cache_t2;


static cache_t2 LL;
static cache_t2 I1;
static cache_t2 D1;

/* By this point, the size/assoc/line_size has been checked. */
static void cachesim_initcache(cache_t config, cache_t2* c)
{
   Int i, j;

   c->size      = config.size;
   c->assoc     = config.assoc;
   c->line_size = config.line_size;

   c->sets           = (c->size / c->line_size) / c->assoc;
   c->sets_min_1     = c->sets - 1;
   c->line_size_bits = VG_(log2)(c->line_size);
   c->tag_shift      = c->line_size_bits + VG_(log2)(c->sets);

   if (c->assoc == 1) {
      VG_(sprintf)(c->desc_line, "%d B, %d B, direct-mapped", 
                                 c->size, c->line_size);
   } else {
      VG_(sprintf)(c->desc_line, "%d B, %d B, %d-way associative",
                                 c->size, c->line_size, c->assoc);
   }

/*   c->tags = VG_(malloc)("cg.sim.ci.1",
                         sizeof(UWord) * c->sets * c->assoc);*/

   c->line_mask = c->line_size - 1;
   c->num_words_per_line = c->line_size / sizeof(UWord);
   c->num_words_bits = VG_(log2)(c->num_words_per_line);

   c->cachelines = VG_(malloc)("cg.sim.ci.1",
                         sizeof(cacheline_t) * c->sets * c->assoc);

   for (i = 0; i < c->sets * c->assoc; i++)
   {
//      c->tags[i] = 0;
        c->cachelines[i].tag = 0;
        c->cachelines[i].bitvector = 0;
        c->cachelines[i].line_num = 0;
        c->cachelines[i].src_line = NULL;
   }

   c->lru_list = VG_(malloc)("cg.sim.ci.2",
                         sizeof(UInt) * c->sets * c->assoc);

   for (i = 0; i < c->sets; i++)
   {
     for (j = 0; j < c->assoc; j++)
       c->lru_list[i * c->assoc + j] = c->assoc - 1 - j;
   }
}

/* This attribute forces GCC to inline the function, getting rid of a
 * lot of indirection around the cache_t2 pointer, if it is known to be
 * constant in the caller (the caller is inlined itself).
 * Without inlining of simulator functions, cachegrind can get 40% slower.
 */
__attribute__((always_inline))
static __inline__
Bool cachesim_setref_is_miss(cache_t2* c, UInt set_no, UWord tag, UInt word_begin, UInt word_end, Int line_num, void* line)
{
   int i, j;
//   UWord *set;
   cacheline_t *cacheline;
   UInt *id;
   UInt tmp, num_words;

//   set = &(c->tags[set_no * c->assoc]);
   cacheline = &(c->cachelines[set_no * c->assoc]);
   id = &(c->lru_list[set_no * c->assoc]);

   /* This loop is unrolled for just the first case, which is the most */
   /* common.  We can't unroll any further because it would screw up   */
   /* if we have a direct-mapped (1-way) cache.                        */
   if (tag == cacheline[id[0]].tag)
   {
      bitop_set_range(&cacheline[id[0]].bitvector, word_begin, word_end);

      /*if (CU_DEBUG && cu_fp && c == &LL) 
         VG_(fprintf)(cu_fp,  "H %lx %x, line: %d, begin: %u, end: %u\n", tag, cacheline[id[0]].bitvector, line_num, word_begin, word_end);*/

      return False;
   }

   /* If the tag is one other than the MRU, move it into the MRU spot  */
   /* and shuffle the rest down.                                       */
   for (i = 1; i < c->assoc; i++) {
      if (tag == cacheline[id[i]].tag) {
         tmp = id[i];
         for (j = i; j > 0; j--) {
            id[j] = id[j - 1];
         }
         id[0] = tmp;

         bitop_set_range(&cacheline[tmp].bitvector, word_begin, word_end);

         /*if (CU_DEBUG && cu_fp && c == &LL) 
            VG_(fprintf)(cu_fp,  "H %lx %x, line: %d, at line: %d, begin: %u, end: %u\n", tag, cacheline[tmp].bitvector, cacheline[tmp].line_num, line_num, word_begin, word_end);*/

         return False;
      }
   }

   /* A miss;  install this tag as MRU, shuffle rest down. */
   UInt evict_id = id[c->assoc - 1];
   cacheline_t evict_line = cacheline[evict_id];
   num_words = bitop_count(evict_line.bitvector);

   if (CU_DEBUG && (!num_words || num_words > MAX_NUM_BINS) && evict_line.tag && cu_fp && c == &D1)
      VG_(fprintf)(cu_fp,  "ERROR: Ev %lx %x, %u, line: %d, %p\n", evict_line.tag, evict_line.bitvector, num_words, evict_line.line_num, evict_line.src_line);

   for (j = c->assoc - 1; j > 0; j--) {
      id[j] = id[j - 1];
   }
   cacheline[evict_id].tag = tag;
   cacheline[evict_id].bitvector = 0;
   cacheline[evict_id].line_num = line_num;
   cacheline[evict_id].src_line = line;
   bitop_set_range(&cacheline[evict_id].bitvector, word_begin, word_end);
   id[0] = evict_id;

   if(evict_line.tag && evict_line.src_line)
   {
     if(c==&D1)
       evict_line.src_line->num_evicts_D1[num_words-1]++;

     if(c==&LL)
       evict_line.src_line->num_evicts_LL[num_words-1]++;

     if (CU_DEBUG && cu_fp && c == &LL) 
       VG_(fprintf)(cu_fp,  "Ev %lx %x, %u, line: %d, %p\n", evict_line.tag, evict_line.bitvector, num_words, evict_line.line_num, evict_line.src_line);
   }

   return True;
}

__attribute__((always_inline))
static __inline__
Bool cachesim_ref_is_miss(cache_t2* c, Addr a, UChar size, Int line_num, LineCC *line)
{
   /* A memory block has the size of a cache line */
   UWord block1 =  a         >> c->line_size_bits;
   UWord block2 = (a+size-1) >> c->line_size_bits;
   UInt  set1   = block1 & c->sets_min_1;

   UWord addr_offset = a & c->line_mask; 
   UWord word_begin = addr_offset >> c->num_words_bits;
   UWord word_end1 = (addr_offset + size - 1) >> c->num_words_bits;

   /* Tags used in real caches are minimal to save space.
    * As the last bits of the block number of addresses mapping
    * into one cache set are the same, real caches use as tag
    *   tag = block >> log2(#sets)
    * But using the memory block as more specific tag is fine,
    * and saves instructions.
    */
   UWord tag1   = block1;

   /*if (CU_DEBUG && cu_fp && c == &LL) 
      VG_(fprintf)(cu_fp,  "Addr %lx, size: %lu\n", a, size);*/

   /* Access entirely within line. */
   if (block1 == block2)
      return cachesim_setref_is_miss(c, set1, tag1, word_begin, word_end1, line_num, line);

   /* Access straddles two lines. */
   else if (block1 + 1 == block2) {
      UInt  set2 = block2 & c->sets_min_1;
      UWord tag2 = block2;

      UWord word_end2 = word_end1;
      word_end1 = ((a & c->line_mask) + c->line_size - 1) >> c->num_words_bits;

      /* always do both, as state is updated as side effect */
      if (cachesim_setref_is_miss(c, set1, tag1, word_begin, word_end1, line_num, line)) {
         cachesim_setref_is_miss(c, set2, tag2, 0, word_end2, line_num, line);
         return True;
      }
      return cachesim_setref_is_miss(c, set2, tag2, 0, word_end2, line_num, line);
   }
   VG_(printf)("addr: %lx  size: %u  blocks: %lu %lu",
               a, size, block1, block2);
   VG_(tool_panic)("item straddles more than two cache sets");
   /* not reached */
   return True;
}

static
void cachesim_collect_undrained_lines(cache_t2* c)
{
   Int i, j;
   UInt id, num_words;
   cacheline_t *cl = c->cachelines;

   for (i = 0; i < c->sets; i++)
   {
     for (j = 0; j < c->assoc; j++)
     {
        id = c->lru_list[i * c->assoc + j];
        if(cl[id].tag && cl[id].src_line) 
        {
           num_words = bitop_count(cl[id].bitvector);
/*           if (CU_DEBUG && (!num_words || num_words > MAX_NUM_BINS) && cu_fp && c == &D1)
              VG_(fprintf)(cu_fp,  "ERROR: Ev %lx %x, %u, line: %d, %p, %llu\n", cl[id].tag, cl[id].bitvector, num_words, cl[id].line_num, cl[id].src_line, cl[id].src_line->num_evicts_D1[num_words-1]);*/

           if(c==&D1)
             cl[id].src_line->num_evicts_D1[num_words-1]++;
           if(c==&LL)
             cl[id].src_line->num_evicts_LL[num_words-1]++;
           if (CU_DEBUG && cu_fp && c == &LL)
              VG_(fprintf)(cu_fp,  "Ev %lx %x, %u, line: %d, %p, %llu\n", cl[id].tag, cl[id].bitvector, num_words, cl[id].line_num, cl[id].src_line, cl[id].src_line->num_evicts_LL[num_words-1]);
        }
     }
   }
}

static void cachesim_initcaches(cache_t I1c, cache_t D1c, cache_t LLc)
{
   cachesim_initcache(I1c, &I1);
   cachesim_initcache(D1c, &D1);
   cachesim_initcache(LLc, &LL);

   open_cu_log();
}

static void cachesim_finish(void)
{
   cachesim_collect_undrained_lines(&D1);
   cachesim_collect_undrained_lines(&LL);
   close_cu_log();
}

__attribute__((always_inline))
static __inline__
void cachesim_I1_doref_Gen(Addr a, UChar size, ULong* m1, ULong *mL)
{
   if (cachesim_ref_is_miss(&I1, a, size, 0, NULL)) {
      (*m1)++;
      if (cachesim_ref_is_miss(&LL, a, size, 0, NULL))
         (*mL)++;
   }
}

// common special case IrNoX
__attribute__((always_inline))
static __inline__
void cachesim_I1_doref_NoX(Addr a, UChar size, ULong* m1, ULong *mL)
{
   UWord block  = a >> I1.line_size_bits;
   UInt  I1_set = block & I1.sets_min_1;

   UWord addr_offset = a & I1.line_mask; 
   UWord word_begin = addr_offset >> I1.num_words_bits;
   UWord word_end = (addr_offset + size - 1) >> I1.num_words_bits;

   // use block as tag
   if (cachesim_setref_is_miss(&I1, I1_set, block, word_begin, word_end, 0, NULL)) {
      UInt  LL_set = block & LL.sets_min_1;
      (*m1)++;
      // can use block as tag as L1I and LL cache line sizes are equal
      if (cachesim_setref_is_miss(&LL, LL_set, block, word_begin, word_end, 0, NULL))
         (*mL)++;
   }
}

__attribute__((always_inline))
static __inline__
Bool cachesim_D1_doref(Addr a, UChar size, ULong* m1, ULong *mL, int line_num, LineCC* line)
{
   if (cachesim_ref_is_miss(&D1, a, size, line_num, line)) {
      (*m1)++;
      if (cachesim_ref_is_miss(&LL, a, size, line_num, line))
         (*mL)++;

      return True;
   }
   return False;
}

/* Check for special case IrNoX. Called at instrumentation time.
 *
 * Does this Ir only touch one cache line, and are L1I/LL cache
 * line sizes the same? This allows to get rid of a runtime check.
 *
 * Returning false is always fine, as this calls the generic case
 */
static Bool cachesim_is_IrNoX(Addr a, UChar size)
{
   UWord block1, block2;

   if (I1.line_size_bits != LL.line_size_bits) return False;
   block1 =  a         >> I1.line_size_bits;
   block2 = (a+size-1) >> I1.line_size_bits;
   if (block1 != block2) return False;

   return True;
}

/*--------------------------------------------------------------------*/
/*--- end                                                 cg_sim.c ---*/
/*--------------------------------------------------------------------*/

