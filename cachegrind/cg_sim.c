
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
      ULong m1_comp, m1_conf, m1_cap;  /* 3 types of cache misses in the first level cache: compulsory, conflict and capacity */
      ULong mL_comp, mL_conf, mL_cap;  /* 3 types of cache misses in the second level cache: compulsory, conflict and capacity */
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

typedef enum {
    MISS_COMPULSORY,
    MISS_CONFLICT,
    MISS_CAPACITY,
    MISS_UNKNOWN
} MissType;

MissType g_last_d1_miss_type = MISS_COMPULSORY;
/* Keep GT available for validation, but allow production/model-only runs to
 * bypass the infinite and fully-associative shadow caches completely.
 */
static Bool d1_ground_truth_enabled = True;

/* Extra lightweight D1 trace context for the Python analysis tool.
 * We keep detailed records only for D1 misses, but count hits between misses
 * to preserve execution-density information without producing a huge hit trace.
 */
static ULong g_d1_access_seq = 0;
static ULong g_d1_hits_since_last_miss = 0;
static Addr  g_last_d1_access_addr = 0;
static UChar g_last_d1_access_size = 0;

typedef enum {
   D1_TRACE_OFF,
   D1_TRACE_ASCII,
   D1_TRACE_BINARY,
   D1_TRACE_COUNTER
} D1TraceMode;

static D1TraceMode d1_trace_mode = D1_TRACE_ASCII;
static const HChar* clo_d1_trace_file = "d1miss.out.%p.bin";
static Int d1_counter_size = 1000;

typedef struct {
   UChar magic[8];
   UInt  version;
   UInt  record_size;
   UInt  cache_sets;
   UInt  cache_ways;
   UInt  cache_line_size;
   UInt  word_size;
   UInt  addr_size;
} D1MissTraceHeader;

typedef struct {
   ULong seq;
   ULong hits_since_last;
   ULong addr;
   ULong tag;
   ULong evicted_addr;
   UInt  set;
   UInt  way;
   Int   evicted_cache_line;
   Int   line_num;
   UInt  size;
   UInt  miss_type;
} D1MissTraceRecord;

#define D1_COUNTER_MAX_SETS       64
#define D1_COUNTER_LINE_SLOTS     16
#define D1_COUNTER_STRIDE_SLOTS   32
#define D1_COUNTER_SAMPLE_SLOTS   4
#define D1_COUNTER_REUSE_SLOTS    (1U << 20)
#define D1_COUNTER_BINARY_BUFFER_RECORDS 256

typedef struct {
   ULong addr;
   ULong evicted_addr;
   ULong seq;
   UInt  hits_since_last;
   Int   line_num;
   UInt  set;
   UInt  way;
   UInt  size;
   UInt  miss_type;
} D1CounterSample;

typedef struct {
   ULong counter_number;
   ULong miss_start;
   ULong seq_start;
   ULong seq_end;
   ULong hits_since_last;
   ULong reuse_miss_sum;
   ULong reuse_seq_sum;
   Long  dominant_stride_bytes;
   UInt  misses;
   UInt  unique_lines;
   UInt  total_evicts;
   UInt  self_evicts;
   UInt  young_evicts;
   UInt  reuse_events;
   UInt  long_reuse_events;
   UInt  exec_reuse_events;
   UInt  long_exec_reuse_events;
   UInt  stride_count;
   UInt  dominant_stride_count;
   UInt  small_stride_count;
   UInt  large_stride_count;
   UInt  distinct_stride_count;
   UInt  access_size_sum;
   UInt  line_slot_count;
   UInt  line_overflow_misses;
   UInt  sample_count;
   UInt  gt_counts[4];
   UShort set_counts[D1_COUNTER_MAX_SETS];
   UShort unique_lines_per_set[D1_COUNTER_MAX_SETS];
   Int   line_numbers[D1_COUNTER_LINE_SLOTS];
   UInt  line_counts[D1_COUNTER_LINE_SLOTS];
   D1CounterSample samples[D1_COUNTER_SAMPLE_SLOTS];
} D1CounterTraceRecord;

typedef struct {
   UChar magic[8];
   UInt  version;
   UInt  record_size;
   UInt  cache_sets;
   UInt  cache_ways;
   UInt  cache_line_size;
   UInt  word_size;
   UInt  addr_size;
   UInt  counter_size;
} D1CounterTraceHeader;

typedef struct {
   ULong cache_line;
   ULong last_miss_index;
   ULong last_seq;
   UInt  valid;
} D1CounterReuseEntry;

typedef struct {
   D1CounterTraceRecord record;
   ULong stride_keys[D1_COUNTER_STRIDE_SLOTS];
   UInt  stride_counts[D1_COUNTER_STRIDE_SLOTS];
} D1CounterState;

#define D1_TRACE_BINARY_BUFFER_RECORDS 1024

static Int d1_trace_binary_fd = -1;
static UInt d1_trace_binary_used = 0;
static D1MissTraceRecord d1_trace_binary_buffer[D1_TRACE_BINARY_BUFFER_RECORDS];
static UInt d1_counter_binary_used = 0;
static D1CounterTraceRecord
   d1_counter_binary_buffer[D1_COUNTER_BINARY_BUFFER_RECORDS];
static D1CounterState d1_counter_state;
static D1CounterReuseEntry* d1_counter_reuse_table = NULL;
static ULong* d1_counter_unique_keys = NULL;
static UInt* d1_counter_unique_epochs = NULL;
static UInt d1_counter_unique_slots = 0;
static UInt d1_counter_unique_mask = 0;
static UInt d1_counter_unique_epoch = 1;
static ULong d1_counter_total_misses = 0;
static ULong d1_counter_number = 0;
static ULong d1_counter_prev_addr = 0;
static Bool d1_counter_prev_addr_valid = False;

static Bool cachesim_d1_trace_set_mode(const HChar* mode)
{
   if (0 == VG_(strcmp)(mode, "off") || 0 == VG_(strcmp)(mode, "no")
       || 0 == VG_(strcmp)(mode, "none")) {
      d1_trace_mode = D1_TRACE_OFF;
      return True;
   }
   if (0 == VG_(strcmp)(mode, "ascii") || 0 == VG_(strcmp)(mode, "text")) {
      d1_trace_mode = D1_TRACE_ASCII;
      return True;
   }
   if (0 == VG_(strcmp)(mode, "binary") || 0 == VG_(strcmp)(mode, "bin")) {
      d1_trace_mode = D1_TRACE_BINARY;
      return True;
   }
   if (0 == VG_(strcmp)(mode, "counter") || 0 == VG_(strcmp)(mode, "summary")
       || 0 == VG_(strcmp)(mode, "period")) {
      d1_trace_mode = D1_TRACE_COUNTER;
      return True;
   }
   return False;
}

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
   Int          word_size_bits;
   cacheline_t  *cachelines;
   UInt         *lru_list;
} cache_t2;


static cache_t2 LL;
static cache_t2 I1;
static cache_t2 D1;

static cache_infi INFI;
static cache_fa FA_D1;
static cache_fa FA_LL;

static const HChar* d1_miss_type_name(MissType miss_type)
{
   switch (miss_type) {
      case MISS_COMPULSORY: return "compulsory";
      case MISS_CONFLICT:   return "conflict";
      case MISS_CAPACITY:   return "capacity";
      case MISS_UNKNOWN:    return "unknown";
      default:              return "unknown";
   }
}

static Bool d1_trace_write_all(Int fd, const void* buf, UInt size)
{
   const UChar* p = (const UChar*)buf;
   UInt remaining = size;

   while (remaining > 0) {
      Int n = VG_(write)(fd, p, remaining);
      if (n <= 0)
         return False;
      p += n;
      remaining -= n;
   }
   return True;
}

static UInt d1_counter_hash(ULong value, UInt mask)
{
   value ^= value >> 33;
   value *= 0xff51afd7ed558ccdULL;
   value ^= value >> 33;
   return ((UInt)value) & mask;
}

static void d1_counter_reset_record(void)
{
   Int i;

   VG_(memset)(&d1_counter_state, 0, sizeof(d1_counter_state));
   d1_counter_state.record.counter_number = d1_counter_number;
   d1_counter_state.record.miss_start = d1_counter_total_misses;
   for (i = 0; i < D1_COUNTER_LINE_SLOTS; i++)
      d1_counter_state.record.line_numbers[i] = -1;

   d1_counter_unique_epoch++;
   if (d1_counter_unique_epoch == 0) {
      if (d1_counter_unique_epochs && d1_counter_unique_slots > 0)
         VG_(memset)(d1_counter_unique_epochs, 0,
                     d1_counter_unique_slots * sizeof(UInt));
      d1_counter_unique_epoch = 1;
   }
}

static void d1_counter_init(void)
{
   UInt slots;

   if (d1_trace_mode != D1_TRACE_COUNTER)
      return;

   if (D1.sets > D1_COUNTER_MAX_SETS) {
      VG_(umsg)(
         "warning: --d1-trace=counter supports at most %d D1 sets; "
         "falling back to per-miss binary mode\n",
         D1_COUNTER_MAX_SETS
      );
      d1_trace_mode = D1_TRACE_BINARY;
      return;
   }

   if (d1_counter_size < 1)
      d1_counter_size = 1000;
   if (d1_counter_size > 65535)
      d1_counter_size = 65535;

   slots = 1;
   while (slots < (UInt)d1_counter_size * 2U)
      slots <<= 1;
   if (slots < 2048)
      slots = 2048;

   d1_counter_unique_slots = slots;
   d1_counter_unique_mask = slots - 1;
   d1_counter_unique_keys = VG_(malloc)(
      "cg.d1.counter.unique.keys", slots * sizeof(ULong)
   );
   d1_counter_unique_epochs = VG_(malloc)(
      "cg.d1.counter.unique.epochs", slots * sizeof(UInt)
   );
   d1_counter_reuse_table = VG_(malloc)(
      "cg.d1.counter.reuse",
      D1_COUNTER_REUSE_SLOTS * sizeof(D1CounterReuseEntry)
   );
   VG_(memset)(d1_counter_unique_epochs, 0, slots * sizeof(UInt));
   VG_(memset)(d1_counter_reuse_table, 0,
               D1_COUNTER_REUSE_SLOTS * sizeof(D1CounterReuseEntry));
   d1_counter_unique_epoch = 1;
   d1_counter_total_misses = 0;
   d1_counter_number = 0;
   d1_counter_prev_addr_valid = False;
   d1_counter_reset_record();
}

static void d1_counter_destroy(void)
{
   if (d1_counter_unique_keys) {
      VG_(free)(d1_counter_unique_keys);
      d1_counter_unique_keys = NULL;
   }
   if (d1_counter_unique_epochs) {
      VG_(free)(d1_counter_unique_epochs);
      d1_counter_unique_epochs = NULL;
   }
   if (d1_counter_reuse_table) {
      VG_(free)(d1_counter_reuse_table);
      d1_counter_reuse_table = NULL;
   }
   d1_counter_unique_slots = 0;
   d1_counter_unique_mask = 0;
}

static void d1_trace_binary_disable_on_error(void)
{
   VG_(umsg)("warning: D1 binary trace write failed; disabling D1 trace output\n");
   if (d1_trace_binary_fd >= 0) {
      VG_(close)(d1_trace_binary_fd);
      d1_trace_binary_fd = -1;
   }
   d1_trace_binary_used = 0;
   d1_counter_binary_used = 0;
   d1_trace_mode = D1_TRACE_OFF;
}

static void d1_trace_binary_flush(void)
{
   UInt bytes;

   if (d1_trace_binary_fd < 0 || d1_trace_binary_used == 0)
      return;

   bytes = d1_trace_binary_used * sizeof(D1MissTraceRecord);
   if (!d1_trace_write_all(d1_trace_binary_fd, d1_trace_binary_buffer, bytes)) {
      d1_trace_binary_disable_on_error();
      return;
   }
   d1_trace_binary_used = 0;
}

static void d1_trace_binary_emit(const D1MissTraceRecord* rec)
{
   if (d1_trace_binary_fd < 0)
      return;

   d1_trace_binary_buffer[d1_trace_binary_used++] = *rec;
   if (d1_trace_binary_used == D1_TRACE_BINARY_BUFFER_RECORDS)
      d1_trace_binary_flush();
}

static void d1_counter_binary_flush(void)
{
   UInt bytes;

   if (d1_trace_binary_fd < 0 || d1_counter_binary_used == 0)
      return;

   bytes = d1_counter_binary_used * sizeof(D1CounterTraceRecord);
   if (!d1_trace_write_all(d1_trace_binary_fd,
                           d1_counter_binary_buffer, bytes)) {
      d1_trace_binary_disable_on_error();
      return;
   }
   d1_counter_binary_used = 0;
}

static void d1_counter_binary_emit(const D1CounterTraceRecord* rec)
{
   if (d1_trace_binary_fd < 0)
      return;

   d1_counter_binary_buffer[d1_counter_binary_used++] = *rec;
   if (d1_counter_binary_used == D1_COUNTER_BINARY_BUFFER_RECORDS)
      d1_counter_binary_flush();
}

static Bool d1_counter_remember_unique(ULong cache_line, UInt set_no)
{
   UInt pos;
   UInt probes;

   if (!d1_counter_unique_epochs || d1_counter_unique_slots == 0)
      return False;

   pos = d1_counter_hash(cache_line, d1_counter_unique_mask);
   for (probes = 0; probes < d1_counter_unique_slots; probes++) {
      if (d1_counter_unique_epochs[pos] != d1_counter_unique_epoch) {
         d1_counter_unique_epochs[pos] = d1_counter_unique_epoch;
         d1_counter_unique_keys[pos] = cache_line;
         d1_counter_state.record.unique_lines++;
         if (set_no < D1_COUNTER_MAX_SETS
             && d1_counter_state.record.unique_lines_per_set[set_no] < 65535)
            d1_counter_state.record.unique_lines_per_set[set_no]++;
         return True;
      }
      if (d1_counter_unique_keys[pos] == cache_line)
         return False;
      pos = (pos + 1) & d1_counter_unique_mask;
   }
   return False;
}

static void d1_counter_remember_line(Int line_num)
{
   UInt pos;
   UInt probes;

   if (line_num <= 0)
      return;
   pos = (((UInt)line_num) * 2654435761U) % D1_COUNTER_LINE_SLOTS;
   for (probes = 0; probes < D1_COUNTER_LINE_SLOTS; probes++) {
      if (d1_counter_state.record.line_numbers[pos] == line_num) {
         d1_counter_state.record.line_counts[pos]++;
         return;
      }
      if (d1_counter_state.record.line_numbers[pos] < 0) {
         d1_counter_state.record.line_numbers[pos] = line_num;
         d1_counter_state.record.line_counts[pos] = 1;
         d1_counter_state.record.line_slot_count++;
         return;
      }
      pos = (pos + 1) % D1_COUNTER_LINE_SLOTS;
   }
   d1_counter_state.record.line_overflow_misses++;
}

static void d1_counter_remember_stride(ULong delta)
{
   UInt pos;
   UInt probes;

   if (delta == 0)
      return;
   d1_counter_state.record.stride_count++;
   if (delta < (ULong)D1.line_size)
      d1_counter_state.record.small_stride_count++;
   else
      d1_counter_state.record.large_stride_count++;

   pos = d1_counter_hash(delta, D1_COUNTER_STRIDE_SLOTS - 1);
   for (probes = 0; probes < D1_COUNTER_STRIDE_SLOTS; probes++) {
      if (d1_counter_state.stride_counts[pos] == 0) {
         d1_counter_state.stride_keys[pos] = delta;
         d1_counter_state.stride_counts[pos] = 1;
         d1_counter_state.record.distinct_stride_count++;
         return;
      }
      if (d1_counter_state.stride_keys[pos] == delta) {
         d1_counter_state.stride_counts[pos]++;
         return;
      }
      pos = (pos + 1) & (D1_COUNTER_STRIDE_SLOTS - 1);
   }
}

static void d1_counter_capture_sample(
   UInt local_index,
   ULong addr,
   ULong evicted_addr,
   UInt set_no,
   UInt way,
   Int line_num
)
{
   UInt slot;

   for (slot = 0; slot < D1_COUNTER_SAMPLE_SLOTS; slot++) {
      UInt target = (slot * (UInt)d1_counter_size)
                    / D1_COUNTER_SAMPLE_SLOTS;
      D1CounterSample* sample;
      if (local_index != target)
         continue;
      if (d1_counter_state.record.sample_count >= D1_COUNTER_SAMPLE_SLOTS)
         return;
      sample = &d1_counter_state.record.samples[
         d1_counter_state.record.sample_count++
      ];
      sample->addr = addr;
      sample->evicted_addr = evicted_addr;
      sample->seq = g_d1_access_seq;
      sample->hits_since_last = (UInt)(
         g_d1_hits_since_last_miss > 0xffffffffULL
         ? 0xffffffffU : g_d1_hits_since_last_miss
      );
      sample->line_num = line_num;
      sample->set = set_no;
      sample->way = way;
      sample->size = (UInt)g_last_d1_access_size;
      sample->miss_type = (UInt)g_last_d1_miss_type;
   }
}

static void d1_counter_flush_record(void)
{
   UInt i;
   UInt best_count = 0;
   ULong best_stride = 0;

   if (d1_counter_state.record.misses == 0)
      return;

   for (i = 0; i < D1_COUNTER_STRIDE_SLOTS; i++) {
      if (d1_counter_state.stride_counts[i] > best_count) {
         best_count = d1_counter_state.stride_counts[i];
         best_stride = d1_counter_state.stride_keys[i];
      }
   }
   d1_counter_state.record.dominant_stride_bytes = (Long)best_stride;
   d1_counter_state.record.dominant_stride_count = best_count;
   d1_counter_binary_emit(&d1_counter_state.record);
   d1_counter_number++;
   d1_counter_reset_record();
}

static void d1_counter_observe(
   UInt set_no,
   UWord tag,
   UInt evict_id,
   ULong evicted_addr,
   Int line_num
)
{
   UInt local_index = d1_counter_state.record.misses;
   UInt reuse_pos;
   D1CounterReuseEntry* reuse_entry;
   ULong miss_distance;
   ULong seq_distance;
   ULong evicted_line;

   if (local_index == 0) {
      d1_counter_state.record.seq_start = g_d1_access_seq;
      d1_counter_state.record.miss_start = d1_counter_total_misses;
   }
   d1_counter_state.record.seq_end = g_d1_access_seq;
   d1_counter_state.record.hits_since_last +=
      g_d1_hits_since_last_miss;
   d1_counter_state.record.access_size_sum +=
      (UInt)g_last_d1_access_size;
   if (set_no < D1_COUNTER_MAX_SETS
       && d1_counter_state.record.set_counts[set_no] < 65535)
      d1_counter_state.record.set_counts[set_no]++;

   d1_counter_remember_unique((ULong)tag, set_no);
   d1_counter_remember_line(line_num);
   if ((UInt)g_last_d1_miss_type < 4)
      d1_counter_state.record.gt_counts[(UInt)g_last_d1_miss_type]++;

   if (d1_counter_prev_addr_valid) {
      ULong addr = (ULong)g_last_d1_access_addr;
      ULong delta = addr >= d1_counter_prev_addr
                    ? addr - d1_counter_prev_addr
                    : d1_counter_prev_addr - addr;
      d1_counter_remember_stride(delta);
   }
   d1_counter_prev_addr = (ULong)g_last_d1_access_addr;
   d1_counter_prev_addr_valid = True;

   if (evicted_addr != 0) {
      d1_counter_state.record.total_evicts++;
      evicted_line = evicted_addr >> D1.line_size_bits;
      if (evicted_line == (ULong)tag)
         d1_counter_state.record.self_evicts++;
      reuse_pos = d1_counter_hash(
         evicted_line, D1_COUNTER_REUSE_SLOTS - 1
      );
      reuse_entry = &d1_counter_reuse_table[reuse_pos];
      if (reuse_entry->valid
          && reuse_entry->cache_line == evicted_line
          && d1_counter_total_misses > reuse_entry->last_miss_index
          && d1_counter_total_misses - reuse_entry->last_miss_index
             <= (ULong)(D1.assoc * 2))
         d1_counter_state.record.young_evicts++;
   }

   reuse_pos = d1_counter_hash(
      (ULong)tag, D1_COUNTER_REUSE_SLOTS - 1
   );
   reuse_entry = &d1_counter_reuse_table[reuse_pos];
   if (reuse_entry->valid && reuse_entry->cache_line == (ULong)tag) {
      miss_distance = d1_counter_total_misses
                      - reuse_entry->last_miss_index;
      seq_distance = g_d1_access_seq - reuse_entry->last_seq;
      d1_counter_state.record.reuse_events++;
      d1_counter_state.record.exec_reuse_events++;
      d1_counter_state.record.reuse_miss_sum += miss_distance;
      d1_counter_state.record.reuse_seq_sum += seq_distance;
      if (miss_distance > (ULong)(D1.assoc * 2))
         d1_counter_state.record.long_reuse_events++;
      if (seq_distance > (ULong)(D1.sets * D1.assoc))
         d1_counter_state.record.long_exec_reuse_events++;
   }
   reuse_entry->cache_line = (ULong)tag;
   reuse_entry->last_miss_index = d1_counter_total_misses;
   reuse_entry->last_seq = g_d1_access_seq;
   reuse_entry->valid = 1;

   d1_counter_capture_sample(
      local_index,
      (ULong)g_last_d1_access_addr,
      evicted_addr,
      set_no,
      evict_id,
      line_num
   );

   d1_counter_state.record.misses++;
   d1_counter_total_misses++;
   if (d1_counter_state.record.misses >= (UInt)d1_counter_size)
      d1_counter_flush_record();
}

static void d1_trace_open_binary_file(void)
{
   HChar* trace_file;
   D1MissTraceHeader miss_header = {
      { 'C', 'G', 'D', '1', 'M', 'I', 'S', 'S' },
      1,
      (UInt)sizeof(D1MissTraceRecord),
      (UInt)D1.sets,
      (UInt)D1.assoc,
      (UInt)D1.line_size,
      (UInt)sizeof(UWord),
      (UInt)sizeof(Addr)
   };
   D1CounterTraceHeader counter_header = {
      { 'C', 'G', 'D', '1', 'C', 'N', 'T', 'R' },
      1,
      (UInt)sizeof(D1CounterTraceRecord),
      (UInt)D1.sets,
      (UInt)D1.assoc,
      (UInt)D1.line_size,
      (UInt)sizeof(UWord),
      (UInt)sizeof(Addr),
      (UInt)d1_counter_size
   };

   if (d1_trace_mode != D1_TRACE_BINARY
       && d1_trace_mode != D1_TRACE_COUNTER)
      return;

   trace_file = VG_(expand_file_name)("--d1-trace-file", clo_d1_trace_file);
   d1_trace_binary_fd = VG_(fd_open)(trace_file,
                                     VKI_O_CREAT|VKI_O_TRUNC|VKI_O_WRONLY,
                                     VKI_S_IRUSR|VKI_S_IWUSR);
   if (d1_trace_binary_fd < 0) {
      VG_(umsg)("error: can't open D1 binary trace file '%s'\n", trace_file);
      VG_(umsg)("       ... D1 trace output will be disabled.\n");
      d1_trace_mode = D1_TRACE_OFF;
      VG_(free)(trace_file);
      return;
   }
   VG_(free)(trace_file);

   if (d1_trace_mode == D1_TRACE_COUNTER) {
      if (!d1_trace_write_all(
             d1_trace_binary_fd, &counter_header, sizeof(counter_header)))
         d1_trace_binary_disable_on_error();
   } else {
      if (!d1_trace_write_all(
             d1_trace_binary_fd, &miss_header, sizeof(miss_header)))
         d1_trace_binary_disable_on_error();
   }
}

static void d1_trace_finish(void)
{
   if (d1_trace_mode == D1_TRACE_COUNTER)
      d1_counter_flush_record();
   d1_counter_binary_flush();
   d1_trace_binary_flush();
   if (d1_trace_binary_fd >= 0) {
      VG_(close)(d1_trace_binary_fd);
      d1_trace_binary_fd = -1;
   }
}

static void emit_d1_miss_trace(cache_t2* c, UInt set_no, UWord tag,
                               UInt evict_id, const cacheline_t* evict_line,
                               Int line_num)
{
   ULong evicted_addr = 0;
   Int evicted_cache_line_number = set_no * c->assoc + evict_id;

   if (evict_line->tag)
      evicted_addr = ((ULong)evict_line->tag) << c->line_size_bits;

   if (d1_trace_mode == D1_TRACE_ASCII) {
      VG_(printf)(
         "D1 MISS: seq=%llu hits_since_last=%llu addr=0x%lx tag=0x%lx size=%u "
         "evicted_addr=0x%llx set=%u way=%u evicted_cache_line=%d "
         "miss_type=%s line_num=%d\n",
         g_d1_access_seq,
         g_d1_hits_since_last_miss,
         g_last_d1_access_addr,
         tag,
         g_last_d1_access_size,
         evicted_addr,
         set_no,
         evict_id,
         evicted_cache_line_number,
         d1_miss_type_name(g_last_d1_miss_type),
         line_num
      );
   } else if (d1_trace_mode == D1_TRACE_BINARY) {
      D1MissTraceRecord rec;
      rec.seq = g_d1_access_seq;
      rec.hits_since_last = g_d1_hits_since_last_miss;
      rec.addr = (ULong)g_last_d1_access_addr;
      rec.tag = (ULong)tag;
      rec.evicted_addr = evicted_addr;
      rec.set = set_no;
      rec.way = evict_id;
      rec.evicted_cache_line = evicted_cache_line_number;
      rec.line_num = line_num;
      rec.size = (UInt)g_last_d1_access_size;
      rec.miss_type = (UInt)g_last_d1_miss_type;
      d1_trace_binary_emit(&rec);
   } else if (d1_trace_mode == D1_TRACE_COUNTER) {
      d1_counter_observe(
         set_no,
         tag,
         evict_id,
         evicted_addr,
         line_num
      );
   }
}

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
   c->word_size_bits = VG_(log2)(sizeof(UWord));

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
      /* D1 hits are not emitted as records; cachesim_D1_doref() keeps a
       * compact hits_since_last count for the next D1 miss.
       */
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
         /* D1 hits are not emitted as records; cachesim_D1_doref() keeps a
          * compact hits_since_last count for the next D1 miss.
          */
         /*if (CU_DEBUG && cu_fp && c == &LL) 
            VG_(fprintf)(cu_fp,  "H %lx %x, line: %d, at line: %d, begin: %u, end: %u\n", tag, cacheline[tmp].bitvector, cacheline[tmp].line_num, line_num, word_begin, word_end);*/

         return False;
      }
   }

   /* A miss;  install this tag as MRU, shuffle rest down. */
   UInt evict_id = id[c->assoc - 1];
   cacheline_t evict_line = cacheline[evict_id];
   num_words = bitop_count(evict_line.bitvector);
   /* Extended D1 miss trace.
    * Fields added for the analysis tool:
    *   seq             : D1 data-access sequence number
    *   hits_since_last : number of D1 hits since previous D1 miss
    *   addr            : raw memory address of the access
    *   tag             : cache-line/block number used by the simulator
    *   size            : access size in bytes
    *
    * We still do not log each hit.  Hits are summarized by hits_since_last.
    */
   if (c == &D1) {
      emit_d1_miss_trace(c, set_no, tag, evict_id, &evict_line, line_num);
      g_d1_hits_since_last_miss = 0;
   }
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
   UWord word_begin = addr_offset >> c->word_size_bits;
   UWord word_end1 = (addr_offset + size - 1) >> c->word_size_bits;

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

      UWord word_end2 = word_end1 - c->num_words_per_line;
      word_end1 = c->num_words_per_line - 1;

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

static void cachefa_initcache(cache_t config, cache_fa* c)
{
   VG_(fprintf)(cu_fp, "cachefa_initcache capacity: %d\n", config.size);
   cachefa_setup(c, (config.size / config.line_size));
}

static void cachesim_initcaches(cache_t I1c, cache_t D1c, cache_t LLc)
{
   open_cu_log();

   cachesim_initcache(I1c, &I1);
   cachesim_initcache(D1c, &D1);
   cachesim_initcache(LLc, &LL);

   if (d1_ground_truth_enabled) {
      cachefa_initcache(D1c, &FA_D1);
      cachefa_initcache(LLc, &FA_LL);
   }

   d1_counter_init();
   d1_trace_open_binary_file();
}

static void cachesim_finish(void)
{
   cachesim_collect_undrained_lines(&D1);
   cachesim_collect_undrained_lines(&LL);
   d1_trace_finish();
   d1_counter_destroy();
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
   UWord word_begin = addr_offset >> I1.word_size_bits;
   UWord word_end = (addr_offset + size - 1) >> I1.word_size_bits;

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
Bool cachesim_D1_doref(Addr a, UChar size, ULong* m1, ULong *mL, int line_num, LineCC* line, CacheCC* cc)
{
   Bool miss_infi = False;
   Bool miss_fa = False;
   Bool miss_fa_LL = False;
   Bool d1_miss;

   /* Count every D1 data access, but only print detailed records on misses. */
   g_d1_access_seq++;
   g_last_d1_access_addr = a;
   g_last_d1_access_size = size;

   if (d1_ground_truth_enabled) {
      miss_infi = cacheinfi_ref_is_miss(&INFI, a, size);
      miss_fa = cachefa_ref_is_miss(&FA_D1, a, size);
      miss_fa_LL = cachefa_ref_is_miss(&FA_LL, a, size);

      /* Set the miss-type before the set-associative D1 lookup, because the
       * extended trace line is emitted inside cachesim_setref_is_miss().
       */
      if (miss_infi)
         g_last_d1_miss_type = MISS_COMPULSORY;
      else if (!miss_fa)
         g_last_d1_miss_type = MISS_CONFLICT;
      else
         g_last_d1_miss_type = MISS_CAPACITY;
   } else {
      g_last_d1_miss_type = MISS_UNKNOWN;
   }

   d1_miss = cachesim_ref_is_miss(&D1, a, size, line_num, line);

   if (d1_miss) {
      (*m1)++;

      if (d1_ground_truth_enabled) {
         if (miss_infi)
            cc->m1_comp++;
         else if (!miss_fa)
            cc->m1_conf++;
         else
            cc->m1_cap++;
      }

      if (cachesim_ref_is_miss(&LL, a, size, line_num, line)) {
         (*mL)++;

         if (d1_ground_truth_enabled) {
            if (miss_infi)
               cc->mL_comp++;
            else if (miss_fa_LL)
               cc->mL_conf++;
            else
               cc->mL_cap++;
         }
      }

      return True;
   }

   /* D1 hit: keep only a compact count until the next D1 miss. */
   g_d1_hits_since_last_miss++;
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
