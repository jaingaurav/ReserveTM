/**
 *  Copyright (C) 2011
 *  University of Rochester Department of Computer Science
 *    and
 *  Lehigh University Department of Computer Science and Engineering
 *
 * License: Modified BSD
 *          Please see the file LICENSE.RSTM for licensing information
 */

#include <setjmp.h>
#include <iostream>
#include <stm/txthread.hpp>
#include <stm/lib_globals.hpp>
#include "policies/policies.hpp"
#include "algs/tml_inline.hpp"
#include "algs/algs.hpp"
#include "inst.hpp"

#if 1
extern "C"  uintptr_t stmreserverange(stm::TxThread* tx,
  uintptr_t addr0,
  uintptr_t addr1)
{
  return tx->reserverange(addr0, addr1);
}

extern "C" void stmreleaserange(stm::TxThread* tx,
  uintptr_t addr0,
  uintptr_t addr1)
{
  tx->releaserange(addr0, addr1);
}

extern "C" void stmreserve01(stm::TxThread* tx,
  int bitmask,
  uintptr_t addr0,
  int instrs,
  int reads,
  int writes
  )
{
  tx->reserve01(bitmask, addr0, instrs, reads, writes);
}

extern "C" void stmreserve02( stm::TxThread* tx, int bitmask,
  uintptr_t addr0,
  uintptr_t addr1,
  int instrs,
  int reads,
  int writes
  )
{
  tx->reserve02(bitmask, addr0, addr1, instrs, reads, writes);
}

extern "C" void stmreserve03( stm::TxThread* tx, int bitmask,
  uintptr_t addr0,
  uintptr_t addr1,
  uintptr_t addr2,
  int instrs,
  int reads,
  int writes
  )
{
  tx->reserve03(bitmask, addr0, addr1, addr2, instrs, reads, writes);
}

extern "C" void stmreserve04(stm::TxThread* tx, int bitmask,
  uintptr_t addr0,
  uintptr_t addr1,
  uintptr_t addr2,
  uintptr_t addr3,
  int instrs,
  int reads,
  int writes
  )
{
  tx->reserve04(bitmask, addr0, addr1, addr2, addr3, instrs, reads, writes);
}

extern "C" void stmreserve05(stm::TxThread* tx, int bitmask,
  uintptr_t addr0,
  uintptr_t addr1,
  uintptr_t addr2,
  uintptr_t addr3,
  uintptr_t addr4,
  int instrs,
  int reads,
  int writes
  )
{
  tx->reserve05(bitmask, addr0, addr1, addr2, addr3, addr4, instrs, reads, writes);
}

extern "C" void stmreserve06(stm::TxThread* tx, int bitmask,
  uintptr_t addr0,
  uintptr_t addr1,
  uintptr_t addr2,
  uintptr_t addr3,
  uintptr_t addr4,
  uintptr_t addr5,
  int instrs,
  int reads,
  int writes
  )
{
  tx->reserve06(bitmask, addr0, addr1, addr2, addr3, addr4, addr5, instrs, reads, writes);
}

extern "C" void stmreserve07(stm::TxThread* tx, int bitmask,
  uintptr_t addr0,
  uintptr_t addr1,
  uintptr_t addr2,
  uintptr_t addr3,
  uintptr_t addr4,
  uintptr_t addr5,
  uintptr_t addr6,
  int instrs,
  int reads,
  int writes
  )
{
  tx->reserve07(bitmask, addr0, addr1, addr2, addr3, addr4, addr5, addr6, instrs, reads, writes);
}

extern "C" int stmreserveclear(stm::TxThread* tx) {
  return tx->reserveclear();
}


#endif

using namespace stm;

namespace
{
  /**
   *  The name of the algorithm with which libstm was initialized
   */
  const char* init_lib_name;

  /**
   *  The default mechanism that libstm uses for an abort. An API environment
   *  may also provide its own abort mechanism (see itm2stm for an example of
   *  how the itm shim does this).
   *
   *  This is ugly because rollback has a configuration-dependent signature.
   */
  NORETURN void
    default_abort_handler(TxThread* tx)
    {
      tx->started = false;
      jmp_buf* scope = (jmp_buf*)TxThread::tmrollback(tx
#if defined(STM_PROTECT_STACK)
        , TOP_OF_ARGS(1)
#endif
#if defined(STM_ABORT_ON_THROW)
        , NULL, 0
#endif
        );
      // need to null out the scope
      longjmp(*scope, 1);
    }
} // (anonymous namespace)

namespace stm
{
  /*** BACKING FOR GLOBAL VARS DECLARED IN TXTHREAD.HPP */
  pad_word_t threadcount          = {0}; // thread count
  TxThread*  threads[MAX_THREADS] = {0}; // all TxThreads
  THREAD_LOCAL_DECL_TYPE(TxThread*) Self; // this thread's TxThread

  /**
   *  Constructor sets up the lists and vars
   */
  TxThread::TxThread()
    : next_id(0), ticket(0), tx_num(0), 
nesting_depth(0),
    allocator(),
    num_commits(0), num_aborts(0), num_restarts(0),
    num_ro(0),

    num_reserved_calls(0),
    num_reserved_reads(0),
    num_reserved_writes(0),
    num_non_reserved_reads(0),
    num_non_reserved_writes(0),
    num_redundant_reserved_reads(0),
    num_redundant_reserved_reads_from_writes(0),
    num_redundant_reserved_writes(0),
    num_redundant_non_reserved_reads(0),
    num_redundant_non_reserved_writes(0),
    num_duplicate_non_reserved_reads(0),
    num_duplicate_non_reserved_writes(0),
    num_writer_stalls(0),
    num_writer_stall_loops(0),
    num_undo_log_entries(0),
    num_skippable_undo_log_entries(0),
    just_logged(0),	
    num_skipped_undo_log_entries(0),
    num_dynamic_merges(0),
    num_saved_log_entries(0),
    range_reserves(0),
    range_reserves_partial(0),
range_reserve_reader_aborts(0),
range_reserves_drain_waits(0),
range_reserves_child_waits(0),
range_reserve_stranger_aborts(0),
    range_dep_reserves(0),
    range_dep_reserve_fails(0),
    range_dep_waits(0),
    range_dep_transfers(0),
    started(false),
    have_ticket(false),
    scope(NULL),
    start_time(0), tmlHasLock(false), undo_log(64), vlist(64), writes(64),
    r_orecs(64), locks(64),
    wf((filter_t*)FILTER_ALLOC(sizeof(filter_t))),
    rf((filter_t*)FILTER_ALLOC(sizeof(filter_t))),
    prio(0), consec_aborts(0), seed((unsigned long)&id), myRRecs(64),
    order(-1), alive(1),
    r_bytelocks(64), w_bytelocks(64), range_bytelocks(64), r_bitlocks(64), w_bitlocks(64),
    my_mcslock(new mcs_qnode_t()),
    cm_ts(INT_MAX),
    cf((filter_t*)FILTER_ALLOC(sizeof(filter_t))),
    nanorecs(64), begin_wait(0), strong_HG(),
    irrevocable(false)
    {
      for (int i = 0; i < 7; ++i)
      {
        num_first_aborts[i] = 0;
        num_read_aborts[i] = 0;
        num_acquire_aborts[i] = 0;
        num_drain_aborts[i] = 0;
        seq_num_r[i] = 0;
        seq_num_w[i] = 0;
        seq_num_range[i] = 0;
      }
      // prevent new txns from starting.
      while (true) {
        int i = curr_policy.ALG_ID;
        if (bcasptr(&tmbegin, stms[i].begin, &begin_blocker))
          break;
        spin64();
      }

      // We need to be very careful here.  Some algorithms (at least TLI and
      // NOrecPrio) like to let a thread look at another thread's TxThread
      // object, even when that other thread is not in a transaction.  We
      // don't want the TxThread object we are making to be visible to
      // anyone, until it is 'ready'.
      //
      // Since those algorithms can only find this TxThread object by looking
      // in threads[], and they scan threads[] by using threadcount.val, we
      // use the following technique:
      //
      // First, only this function can ever change threadcount.val.  It does
      // not need to do so atomically, but it must do so from inside of the
      // critical section created by the begin_blocker CAS
      //
      // Second, we can predict threadcount.val early, but set it late.  Thus
      // we can completely configure this TxThread, and even put it in the
      // threads[] array, without writing threadcount.val.
      //
      // Lastly, when we finally do write threadcount.val, we make sure to
      // preserve ordering so that write comes after initialization, but
      // before lock release.

      // predict the new value of threadcount.val
      id = threadcount.val + 1;

      // update the allocator
      allocator.setID(id-1);

      // set up my lock word
      my_lock.fields.lock = 1;
      my_lock.fields.id = id;

      // clear filters
      wf->clear();
      rf->clear();

      // configure my TM instrumentation
      install_algorithm_local(curr_policy.ALG_ID, this);

      // set the pointer to this TxThread
      threads[id-1] = this;

      // set the epoch to default
      epochs[id-1].val = EPOCH_MAX;

      // NB: at this point, we could change the mode based on the thread
      //     count.  The best way to do so would be to install ProfileTM.  We
      //     would need to be very careful, though, in case another thread is
      //     already running ProfileTM.  We'd also need a way to skip doing
      //     so if a non-adaptive policy was in place.  An even better
      //     strategy might be to put a request for switching outside the
      //     critical section, as the last line of this method.
      //
      // NB: For the release, we are omitting said code, as it does not
      //     matter in the workloads we provide.  We should revisit at some
      //     later time.

      // now publish threadcount.val
      CFENCE;
      threadcount.val = id;

      // now we can let threads progress again
      CFENCE;
      tmbegin = stms[curr_policy.ALG_ID].begin;
    }

  /*** print a message and die */
  void UNRECOVERABLE(const char* msg)
  {
    std::cerr << msg << std::endl;
    exit(-1);
  }

  /***  GLOBAL FUNCTION POINTERS FOR OUR INDIRECTION-BASED MODE SWITCHING */

  /**
   *  The begin function pointer.  Note that we need tmbegin to equal
   *  begin_cgl initially, since "0" is the default algorithm
   */
  bool TM_FASTCALL (*volatile TxThread::tmbegin)(TxThread*) = begin_CGL;

  /**
   *  The tmrollback, tmabort, and tmirrevoc pointers
   */
  scope_t* (*TxThread::tmrollback)(STM_ROLLBACK_SIG(,,,));
  NORETURN void (*TxThread::tmabort)(TxThread*) = default_abort_handler;
  bool (*TxThread::tmirrevoc)(STM_IRREVOC_SIG(,)) = NULL;

  /*** the init factory */
  void TxThread::thread_init()
  {
    // multiple inits from one thread do not cause trouble
    if (Self) return;

    // create a TxThread and save it in thread-local storage
    Self = new TxThread();
  }

  /**
   *  Simplified support for self-abort
   */
  void restart()
  {
    // get the thread's tx context
    TxThread* tx = Self;
    // register this restart
    ++tx->num_restarts;
    // call the abort code
    tx->tmabort(tx);
  }


  void begin(TxThread* tx, scope_t* s, uint32_t /*abort_flags*/)
  {
    if (++tx->nesting_depth > 1)
      return;

    // we must ensure that the write of the transaction's scope occurs
    // *before* the read of the begin function pointer.  On modern x86, a
    // CAS is faster than using WBR or xchg to achieve the ordering.  On
    // SPARC, WBR is best.
#ifdef STM_CPU_SPARC
    tx->scope = s; WBR;
#else
    // NB: this CAS fails on a transaction restart... is that too expensive?
    casptr((volatile uintptr_t*)&tx->scope, (uintptr_t)0, (uintptr_t)s);
#endif

    // some adaptivity mechanisms need to know nontransactional and
    // transactional time.  This code suffices, because it gets the time
    // between transactions.  If we need the time for a single transaction,
    // we can run ProfileTM
    if (tx->end_txn_time)
      tx->total_nontxn_time += (tick() - tx->end_txn_time);

    // now call the per-algorithm begin function
    TxThread::tmbegin(tx);
  }

  void commit(TxThread* tx)
  {
    // don't commit anything if we're nested... just exit this scope
    if (--tx->nesting_depth)
      return;

    // dispatch to the appropriate end function
#ifdef STM_PROTECT_STACK
    void* top_of_stack;
    tx->commit(&top_of_stack);
#else
    tx->commit();
#endif

    // zero scope (to indicate "not in tx")
    CFENCE;
    tx->scope = NULL;

    // record start of nontransactional time
    tx->end_txn_time = tick();
  }

  void* tx_alloc(size_t size) { return Self->allocator.txAlloc(size); }

  void tx_free(void* p) { Self->allocator.txFree(p); }


  /**
   *  When the transactional system gets shut down, we call this to dump stats
   */
  void sys_shutdown()
  {
    static volatile unsigned int mtx = 0;
    while (!bcas32(&mtx, 0u, 1u)) { }

    uint64_t nontxn_count = 0;                // time outside of txns
    uint32_t pct_ro       = 0;                // read only txn ratio
    uint32_t txn_count    = 0;                // total txns
    uint32_t rw_txns      = 0;                // rw commits
    uint32_t ro_txns      = 0;                // ro commits
    for (uint32_t i = 0; i < threadcount.val; i++) {
      std::cout << "Thread: "       << threads[i]->id
        << "; RW Commits: " << threads[i]->num_commits
        << "; RO Commits: " << threads[i]->num_ro
        << "; Aborts: "     << threads[i]->num_aborts
        << "; Restarts: "   << threads[i]->num_restarts
        << std::endl;
      std::cout << "rc: "       << threads[i]->num_reserved_calls
#if 0
        << "; rr: "       << threads[i]->num_reserved_reads      
        << "; rw: " << threads[i]->num_reserved_writes
        << "; nrr: " << threads[i]->num_non_reserved_reads
        << "; nrw: "     << threads[i]->num_non_reserved_writes
        << "; rrr: "       << threads[i]->num_redundant_reserved_reads
        << "; rrr(fw): "       << threads[i]->num_redundant_reserved_reads_from_writes
        << "; rrw: " << threads[i]->num_redundant_reserved_writes
        << "; rnrr: " << threads[i]->num_redundant_non_reserved_reads
        << "; rnrw: "     << threads[i]->num_redundant_non_reserved_writes
        << "; dnrr: " << threads[i]->num_duplicate_non_reserved_reads
        << "; dnrw: "     << threads[i]->num_duplicate_non_reserved_writes
#endif
        << "; nws: " << threads[i]->num_writer_stalls
        << "; nwsl: " << threads[i]->num_writer_stall_loops
        << "; nule: " << threads[i]->num_undo_log_entries
        << "; nsule: " << threads[i]->num_skippable_undo_log_entries
        << "; nsdule: " << threads[i]->num_skipped_undo_log_entries
        << "; dm: " << threads[i]->num_dynamic_merges << std::endl
        << "ABORTS" << std::endl
        << "Saved log entries: " << threads[i]->num_saved_log_entries << std::endl
        << "First aborts: "
        << " [" << threads[i]->num_first_aborts[0]
        << ", " << threads[i]->num_first_aborts[1]
        << ", " << threads[i]->num_first_aborts[2]
        << ", " << threads[i]->num_first_aborts[3]
        << ", " << threads[i]->num_first_aborts[4]
        << ", " << threads[i]->num_first_aborts[5]
        << ", " << threads[i]->num_first_aborts[6] << "]" << std::endl
        << "Read aborts:"
        << " [" << threads[i]->num_read_aborts[0]
        << ", " << threads[i]->num_read_aborts[1]
        << ", " << threads[i]->num_read_aborts[2]
        << ", " << threads[i]->num_read_aborts[3]
        << ", " << threads[i]->num_read_aborts[4]
        << ", " << threads[i]->num_read_aborts[5]
        << ", " << threads[i]->num_read_aborts[6] << "]" << std::endl
        << "Acquire aborts:"
        << " [" << threads[i]->num_acquire_aborts[0]
        << ", " << threads[i]->num_acquire_aborts[1]
        << ", " << threads[i]->num_acquire_aborts[2]
        << ", " << threads[i]->num_acquire_aborts[3]
        << ", " << threads[i]->num_acquire_aborts[4]
        << ", " << threads[i]->num_acquire_aborts[5]
        << ", " << threads[i]->num_acquire_aborts[6] << "]" << std::endl
        << "Drain aborts:"
        << " [" << threads[i]->num_drain_aborts[0]
        << ", " << threads[i]->num_drain_aborts[1]
        << ", " << threads[i]->num_drain_aborts[2]
        << ", " << threads[i]->num_drain_aborts[3]
        << ", " << threads[i]->num_drain_aborts[4]
        << ", " << threads[i]->num_drain_aborts[5]
        << ", " << threads[i]->num_drain_aborts[6] << "]" << std::endl
        << "Aborts on read:"
        << " [" << threads[i]->seq_num_r[0]
        << ", " << threads[i]->seq_num_r[1]
        << ", " << threads[i]->seq_num_r[2]
        << ", " << threads[i]->seq_num_r[3]
        << ", " << threads[i]->seq_num_r[4]
        << ", " << threads[i]->seq_num_r[5]
        << ", " << threads[i]->seq_num_r[6] << "]" << std::endl
        << "Aborts on write:"
        << " [" << threads[i]->seq_num_w[0]
        << ", " << threads[i]->seq_num_w[1]
        << ", " << threads[i]->seq_num_w[2]
        << ", " << threads[i]->seq_num_w[3]
        << ", " << threads[i]->seq_num_w[4]
        << ", " << threads[i]->seq_num_w[5]
        << ", " << threads[i]->seq_num_w[6] << "]" << std::endl
        << "Aborts on range (write):"
        << " [" << threads[i]->seq_num_range[0]
        << ", " << threads[i]->seq_num_range[1]
        << ", " << threads[i]->seq_num_range[2]
        << ", " << threads[i]->seq_num_range[3]
        << ", " << threads[i]->seq_num_range[4]
        << ", " << threads[i]->seq_num_range[5]
        << ", " << threads[i]->seq_num_range[6] << "]" << std::endl
        << "RANGE RESERVES" << std::endl
        << "#: " << threads[i]->range_reserves
        << " # partial: " << threads[i]->range_reserves_partial
        << " RdAbt: " << threads[i]->range_reserve_reader_aborts
        << " DrWait: " << threads[i]->range_reserves_drain_waits
        << " ChWait: " << threads[i]->range_reserves_child_waits
        << " StrAbt: " << threads[i]->range_reserve_stranger_aborts
        << " DepRSV: " << threads[i]->range_dep_reserves
        << " DepRSVFail: " << threads[i]->range_dep_reserve_fails
        << " DepWait: " << threads[i]->range_dep_waits
        << " DepTrans: " << threads[i]->range_dep_transfers << std::endl;
      threads[i]->abort_hist.dump();
      rw_txns += threads[i]->num_commits;
      ro_txns += threads[i]->num_ro;
      nontxn_count += threads[i]->total_nontxn_time;
    }
    txn_count = rw_txns + ro_txns;
    pct_ro = (!txn_count) ? 0 : (100 * ro_txns) / txn_count;

    std::cout << "Total nontxn work:\t" << nontxn_count << std::endl;

    // if we ever switched to ProfileApp, then we should print out the
    // ProfileApp custom output.
    if (app_profiles) {
      uint32_t divisor =
        (curr_policy.ALG_ID == ProfileAppAvg) ? txn_count : 1;
      if (divisor == 0)
        divisor = 0u - 1u; // unsigned infinity :)

      std::cout << "# " << stms[curr_policy.ALG_ID].name << " #" << std::endl;
      std::cout << "# read_ro, read_rw_nonraw, read_rw_raw, write_nonwaw, write_waw, txn_time, "
        << "pct_txtime, roratio #" << std::endl;
      std::cout << app_profiles->read_ro  / divisor << ", "
        << app_profiles->read_rw_nonraw / divisor << ", "
        << app_profiles->read_rw_raw / divisor << ", "
        << app_profiles->write_nonwaw / divisor << ", "
        << app_profiles->write_waw / divisor << ", "
        << app_profiles->txn_time / divisor << ", "
        << ((100*app_profiles->timecounter)/nontxn_count) << ", "
        << pct_ro << " #" << std::endl;
    }
    CFENCE;
    mtx = 0;
  }

  /**
   *  for parsing input to determine the valid algorithms for a phase of
   *  execution.
   *
   *  Setting a policy is a lot like changing algorithms, but requires a little
   *  bit of custom synchronization
   */
  void set_policy(const char* phasename)
  {
    // prevent new txns from starting.  Note that we can't be in ProfileTM
    // while doing this
    while (true) {
      int i = curr_policy.ALG_ID;
      if (i == ProfileTM)
        continue;
      if (bcasptr(&TxThread::tmbegin, stms[i].begin, &begin_blocker))
        break;
      spin64();
    }

    // wait for everyone to be out of a transaction (scope == NULL)
    for (unsigned i = 0; i < threadcount.val; ++i)
      while (threads[i]->scope)
        spin64();

    // figure out the algorithm for the STM, and set the adapt policy

    // we assume that the phase is a single-algorithm phase
    int new_algorithm = stm_name_map(phasename);
    int new_policy = Single;
    if (new_algorithm == -1) {
      int tmp = pol_name_map(phasename);
      if (tmp == -1)
        UNRECOVERABLE("Invalid configuration string");
      new_policy = tmp;
      new_algorithm = pols[tmp].startmode;
    }

    curr_policy.POL_ID = new_policy;
    curr_policy.waitThresh = pols[new_policy].waitThresh;
    curr_policy.abortThresh = pols[new_policy].abortThresh;

    // install the new algorithm
    install_algorithm(new_algorithm, Self);
  }

  /**
   *  Template Metaprogramming trick for initializing all STM algorithms.
   *
   *  This is either a very gross trick, or a very cool one.  We have ALG_MAX
   *  algorithms, and they all need to be initialized.  Each has a unique
   *  identifying integer, and each is initialized by calling an instantiation
   *  of initTM<> with that integer.
   *
   *  Rather than call each function through a line of code, we use a
   *  tail-recursive template: When we call MetaInitializer<0>.init(), it will
   *  recursively call itself for every X, where 0 <= X < ALG_MAX.  Since
   *  MetaInitializer<X>::init() calls initTM<X> before recursing, this
   *  instantiates and calls the appropriate initTM function.  Thus we
   *  correctly call all initialization functions.
   *
   *  Furthermore, since the code is tail-recursive, at -O3 g++ will inline all
   *  the initTM calls right into the sys_init function.  While the code is not
   *  performance critical, it's still nice to avoid the overhead.
   */
  template <int I = 0>
    struct MetaInitializer
    {
      /*** default case: init the Ith tm, then recurse to I+1 */
      static void init()
      {
        initTM<(stm::ALGS)I>();
        MetaInitializer<(stm::ALGS)I+1>::init();
      }
    };
  template <>
    struct MetaInitializer<ALG_MAX>
    {
      /*** termination case: do nothing for ALG_MAX */
      static void init() { }
    };

  /**
   *  Initialize the TM system.
   */
  void sys_init(stm::AbortHandler conflict_abort_handler)
  {
    static volatile uint32_t mtx = 0;

    if (bcas32(&mtx, 0u, 1u)) {
      // manually register all behavior policies that we support.  We do
      // this via tail-recursive template metaprogramming
      MetaInitializer<0>::init();

      // guess a default configuration, then check env for a better option
      const char* cfg = "NOrec";
      const char* configstring = getenv("STM_CONFIG");
      if (configstring)
        cfg = configstring;
      else
        printf("STM_CONFIG environment variable not found... using %s\n", cfg);
      init_lib_name = cfg;

      // now initialize the the adaptive policies
      pol_init(cfg);

      // this is (for now) how we make sure we have a buffer to hold
      // profiles.  This also specifies how many profiles we do at a time.
      char* spc = getenv("STM_NUMPROFILES");
      if (spc != NULL)
        profile_txns = strtol(spc, 0, 10);
      profiles = (dynprof_t*)malloc(profile_txns * sizeof(dynprof_t));
      for (unsigned i = 0; i < profile_txns; i++)
        profiles[i].clear();

      // Initialize the global abort handler.
      if (conflict_abort_handler)
        TxThread::tmabort = conflict_abort_handler;

      // now set the phase
      set_policy(cfg);

      printf("STM library configured using config == %s\n", cfg);

      mtx = 2;
    }
    while (mtx != 2) { }
  }

  /**
   *  Return the name of the algorithm with which the library was configured
   */
  const char* get_algname()
  {
    return init_lib_name;
  }

} // namespace stm
