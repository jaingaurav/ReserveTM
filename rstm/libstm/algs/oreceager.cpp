/**
 *  Copyright (C) 2011
 *  University of Rochester Department of Computer Science
 *    and
 *  Lehigh University Department of Computer Science and Engineering
 *
 * License: Modified BSD
 *          Please see the file LICENSE.RSTM for licensing information
 */

/**
 *  OrecEager Implementation:
 *
 *    This STM is similar to LSA/TinySTM and to the algorithm published by
 *    Wang et al. at CGO 2007.  The algorithm uses a table of orecs, direct
 *    update, encounter time locking, and undo logs.
 *
 *    The principal difference is in how OrecEager handles the modification
 *    of orecs when a transaction aborts.  In Wang's algorithm, a thread at
 *    commit time will first validate, then increment the counter.  This
 *    allows for threads to skip prevalidation of orecs in their read
 *    functions... however, it necessitates good CM, because on abort, a
 *    transaction must run its undo log, then get a new timestamp, and then
 *    release all orecs at that new time.  In essence, the aborted
 *    transaction does "silent stores", and these stores can cause other
 *    transactions to abort.
 *
 *    In LSA/TinySTM, each orec includes an "incarnation number" in the low
 *    bits.  When a transaction aborts, it runs its undo log, then it
 *    releases all locks and bumps the incarnation number.  If this results
 *    in incarnation number wraparound, then the abort function must
 *    increment the timestamp in the orec being released.  If this timestamp
 *    is larger than the current max timestamp, the aborting transaction must
 *    also bump the timestamp.  This approach has a lot of corner cases, but
 *    it allows for the abort-on-conflict contention manager.
 *
 *    In our code, we skip the incarnation numbers, and simply say that when
 *    releasing locks after undo, we increment each, and we keep track of the
 *    max value written.  If the value is greater than the timestamp, then at
 *    the end of the abort code, we increment the timestamp.  A few simple
 *    invariants about time ensure correctness.
*/

#include "../profiling.hpp"
#include "../cm.hpp"
#include "algs.hpp"

using stm::TxThread;
using stm::timestamp;
using stm::OrecList;
using stm::orec_t;
using stm::get_orec;
using stm::id_version_t;
using stm::UndoLogEntry;


/**
 *  Declare the functions that we're going to implement, so that we can avoid
 *  circular dependencies.
 *
 *  NB: OrecEager actually does better without fine-grained switching for
 *      read-only transactions, so we don't support the read-only optimization
 *      in this code.
 */
namespace {
  template <class CM>
    struct OrecEager_Generic
    {
      static TM_FASTCALL bool begin(TxThread*);
      static TM_FASTCALL void commit(STM_COMMIT_SIG(,));
      static void initialize(int id, const char* name);
      static stm::scope_t* rollback(STM_ROLLBACK_SIG(,,,));
    };

  TM_FASTCALL void* read(STM_READ_SIG(,,));
  TM_FASTCALL void write(STM_WRITE_SIG(,,,));
  //static TM_FASTCALL int reserverange(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, int size, int instrs, int reads, int writes);
  static TM_FASTCALL int reserve01(TxThread* tx, int bitmask, uintptr_t addr0, int instrs, int reads, int writes);
  static TM_FASTCALL int reserve02(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, int instrs, int reads, int writes);
  static TM_FASTCALL int reserve03(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, int instrs, int reads, int writes);
  static TM_FASTCALL int reserve04(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, uintptr_t addr3, int instrs, int reads, int writes);
  static TM_FASTCALL int reserveclear(TxThread* tx);
  bool irrevoc(STM_IRREVOC_SIG(,));
  NOINLINE void validate(TxThread*);
  void onSwitchTo();

  // -----------------------------------------------------------------------------
  // OrecEager implementation
  // -----------------------------------------------------------------------------
  template <class CM>
    void
    OrecEager_Generic<CM>::initialize(int id, const char* name)
    {
      // set the name
      stm::stms[id].name      = name;

      // set the pointers
      stm::stms[id].begin     = OrecEager_Generic<CM>::begin;
      stm::stms[id].commit    = OrecEager_Generic<CM>::commit;
      stm::stms[id].rollback  = OrecEager_Generic<CM>::rollback;

      stm::stms[id].read      = read;
      stm::stms[id].write     = write;
      //stm::stms[id].reserverange = reserverange;
      stm::stms[id].reserve01 = reserve01;
      stm::stms[id].reserve02 = reserve02;
      stm::stms[id].reserve03 = reserve03;
      stm::stms[id].reserve04 = reserve04;
      stm::stms[id].reserveclear = reserveclear;
      stm::stms[id].irrevoc   = irrevoc;
      stm::stms[id].switcher  = onSwitchTo;
      stm::stms[id].privatization_safe = false;
    }

  template <class CM>
    bool
    OrecEager_Generic<CM>::begin(TxThread* tx)
    {
      tx->started = true;
      // sample the timestamp and prepare local structures
      tx->allocator.onTxBegin();
      tx->start_time = timestamp.val;
      CM::onBegin(tx);
      return false;
    }

  /**
   *  OrecEager commit:
   *
   *    read-only transactions do no work
   *
   *    writers must increment the timestamp, maybe validate, and then release
   *    locks
   */
  template <class CM>
    void
    OrecEager_Generic<CM>::commit(STM_COMMIT_SIG(tx,))
    {
      // use the lockset size to identify if tx is read-only
      if (!tx->locks.size()) {
        CM::onCommit(tx);
        tx->r_orecs.reset();
        OnReadOnlyCommit(tx);
        return;
      }

      // increment the global timestamp
      uintptr_t end_time = 1 + faiptr(&timestamp.val);

      // skip validation if nobody else committed since my last validation
      if (end_time != (tx->start_time + 1)) {
        foreach (OrecList, i, tx->r_orecs) {
          // abort unless orec older than start or owned by me
          uintptr_t ivt = (*i)->v.all;
          if ((ivt > tx->start_time) && (ivt != tx->my_lock.all))
            tx->tmabort(tx);
        }
      }

      // release locks
      foreach (OrecList, i, tx->locks)
        (*i)->v.all = end_time;

      // notify CM
      CM::onCommit(tx);

      // reset lock list and undo log
      tx->locks.reset();
      tx->undo_log.reset();
      // reset read list, do common cleanup
      tx->r_orecs.reset();
      OnReadWriteCommit(tx);
    }

  /**
   *  OrecEager read:
   *
   *    Must check orec twice, and may need to validate
   */
  void*
    read(STM_READ_SIG(tx,addr,))
    {
#if 1
      tx->reserve01(0x0, (uintptr_t)addr, 1000, 1000, 1000);
          CFENCE;
      return *addr;
#else
      // get the orec addr, then start loop to read a consistent value
      orec_t* o = get_orec(addr);
      while (true) {
        // read the orec BEFORE we read anything else
        id_version_t ivt;
        ivt.all = o->v.all;
        CFENCE;

        // read the location
        void* tmp = *addr;

        // best case: I locked it already
        if (ivt.all == tx->my_lock.all)
          return tmp;

        // re-read orec AFTER reading value
        CFENCE;
        uintptr_t ivt2 = o->v.all;

        // common case: new read to an unlocked, old location
        if ((ivt.all == ivt2) && (ivt.all <= tx->start_time)) {
          tx->r_orecs.insert(o);
          return tmp;
        }

        // abort if locked
        if (__builtin_expect(ivt.fields.lock, 0))
          tx->tmabort(tx);

        // scale timestamp if ivt is too new, then try again
        uintptr_t newts = timestamp.val;
        validate(tx);
        tx->start_time = newts;
      }
#endif
    }

  /**
   *  OrecEager write:
   *
   *    Lock the orec, log the old value, do the write
   */
  void
    write(STM_WRITE_SIG(tx,addr,val,mask))
    {
#if 1
      tx->reserve01(0x1, (uintptr_t)addr, 1000, 1000, 1000);
          CFENCE;
      STM_DO_MASKED_WRITE(addr, val, mask);
#else
      // get the orec addr, then enter loop to get lock from a consistent state
      orec_t* o = get_orec(addr);
      while (true) {
        // read the orec version number
        id_version_t ivt;
        ivt.all = o->v.all;

        // common case: uncontended location... try to lock it, abort on fail
        if (ivt.all <= tx->start_time) {
          if (!bcasptr(&o->v.all, ivt.all, tx->my_lock.all))
            tx->tmabort(tx);

          // save old value, log lock, do the write, and return
          o->p = ivt.all;
          tx->locks.insert(o);
          tx->undo_log.insert(UndoLogEntry(STM_UNDO_LOG_ENTRY(addr, *addr, mask)));
          STM_DO_MASKED_WRITE(addr, val, mask);
          return;
        }

        // next best: I already have the lock... must log old value, because
        // many locations hash to the same orec.  The lock does not mean I
        // have undo logged *this* location
        if (ivt.all == tx->my_lock.all) {
          tx->undo_log.insert(UndoLogEntry(STM_UNDO_LOG_ENTRY(addr, *addr, mask)));
          STM_DO_MASKED_WRITE(addr, val, mask);
          return;
        }

        // fail if lock held by someone else
        if (ivt.fields.lock)
          tx->tmabort(tx);

        // unlocked but too new... scale forward and try again
        uintptr_t newts = timestamp.val;
        validate(tx);
        tx->start_time = newts;
      }
#endif
    }

  int reserveclear(TxThread*tx) {
    // use the lockset size to identify if tx is read-only
    if (!tx->locks.size()) {
      //CM::onCommit(tx);
      tx->r_orecs.reset();
      tx->allocator.onTxCommit();
      tx->abort_hist.onCommit(tx->consec_aborts);
      tx->consec_aborts = 0;
      ++tx->num_ro;
      return 1;
    }

    // increment the global timestamp
    uintptr_t end_time = 1 + faiptr(&timestamp.val);

    // skip validation if nobody else committed since my last validation
    if (end_time != (tx->start_time + 1)) {
      foreach (OrecList, i, tx->r_orecs) {
        // abort unless orec older than start or owned by me
        uintptr_t ivt = (*i)->v.all;
        if ((ivt > tx->start_time) && (ivt != tx->my_lock.all))
          return 0;
      }
    }

    // release locks
    foreach (OrecList, i, tx->locks)
      (*i)->v.all = end_time;

    // notify CM
    //CM::onCommit(tx);

    // reset lock list and undo log
    tx->locks.reset();
    tx->undo_log.reset();
    // reset read list, do common cleanup
    tx->r_orecs.reset();
    tx->allocator.onTxCommit();
    tx->abort_hist.onCommit(tx->consec_aborts);
    tx->consec_aborts = 0;
    ++tx->num_commits;
    //tx->setReadWriteCommit(read_ro, write_ro, commit_ro);
    return 1;
  }
/*
  int
    reserverange(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, int size, int instrs, int reads, int writes)
    {
      //fprintf(stderr, "reserverange- start: addr0=%p, addr1=%p", addr0, addr1);
      uintptr_t addr = addr0;
      int next = 2;
      int prev = 1; 
      do {
        if (next != prev) {
          //fprintf(stderr, "reserverange- new: addr=%p", addr);
          reserve01(tx, bitmask, addr, instrs, reads, writes);
          prev  = addr >> 3;
        }
        else {
          //fprintf(stderr, "reserverange- old: addr=%p", addr);
        }
        addr += size;
        next = addr >> 3;
      } while (addr <=  addr1);

      return 0;
    }
*/
  int
    reserve01(TxThread* tx, int bitmask, uintptr_t addr0, int instrs, int reads, int writes)
    {
      //TODO: This has to be generic
#ifdef SHORT_TRANS      
if (!tx->started)
      {
        tx->allocator.onTxBegin();
        tx->start_time = timestamp.val;
      }
#endif
      //bool over = false;
#if 0
      if (bitmask > 4)  {  
        bitmask -= 4;
        over = false;

        fprintf(stderr, "XXX %d tx= %p, bitmask=%d, addr0=%p, val=%x\n", reads, tx, bitmask, addr0, (void*)*(long *)addr0);
        //bitmask = 0;
        //*(int*)bitmask = 1;
      } else {
        //fprintf(stderr, "%d tx= %p, bitmask=%d, addr0=%p, val=%p\n", reads, tx, bitmask, addr0, (void*)*(long *)addr0);
      }
#endif
      void **addr = (void **) addr0;
      orec_t* o = get_orec(addr);
      if (!(bitmask & 1)) {
        // get the orec addr, then start loop to read a consistent value
        while (true) {
          // read the orec BEFORE we read anything else
          id_version_t ivt;
          ivt.all = o->v.all;
          CFENCE;

          // best case: I locked it already
          if (ivt.all == tx->my_lock.all)
            return 1;

          // re-read orec AFTER reading value
          CFENCE;
          uintptr_t ivt2 = o->v.all;

          // common case: new read to an unlocked, old location
          if ((ivt.all == ivt2) && (ivt.all <= tx->start_time)) {
            tx->r_orecs.insert(o);
            return 1;
          }

          // abort if locked
          if (__builtin_expect(ivt.fields.lock, 0)) {
            //++tx->num_reserve_aborts[instrs-1];
#ifdef SHORT_TRANS      
            if (!tx->started)
              return 0;
            else
#endif
              tx->tmabort(tx);
          }

          // scale timestamp if ivt is too new, then try again
          uintptr_t newts = timestamp.val;
          validate(tx);
          tx->start_time = newts;
        }
      }
      else
      {
        // get the orec addr, then enter loop to get lock from a consistent state
        while (true) {
          // read the orec version number
          id_version_t ivt;
          ivt.all = o->v.all;

          // common case: uncontended location... try to lock it, abort on fail
          if (ivt.all <= tx->start_time) {
            if (!bcasptr(&o->v.all, ivt.all, tx->my_lock.all)) {
              //++tx->num_reserve_aborts[instrs-1];
#ifdef SHORT_TRANS      
            if (!tx->started)
              return 0;
            else
#endif
                tx->tmabort(tx);
            }

            // save old value, log lock, do the write, and return
            o->p = ivt.all;
            tx->locks.insert(o);
            tx->undo_log.insert(UndoLogEntry(STM_UNDO_LOG_ENTRY(addr, *addr, mask)));
            return 1;
          }

          // next best: I already have the lock... must log old value, because
          // many locations hash to the same orec.  The lock does not mean I
          // have undo logged *this* location
          if (ivt.all == tx->my_lock.all) {
            tx->undo_log.insert(UndoLogEntry(STM_UNDO_LOG_ENTRY(addr, *addr, mask)));
            return 1;
          }

          // fail if lock held by someone else
          if (ivt.fields.lock) {
            //++tx->num_reserve_aborts[instrs-1];
#ifdef SHORT_TRANS      
            if (!tx->started)
              return 0;
            else
#endif
              tx->tmabort(tx);
          }

          // unlocked but too new... scale forward and try again
          uintptr_t newts = timestamp.val;
          validate(tx);
          tx->start_time = newts;
        }
      }

      return 1;
      //if (over)
      //fprintf(stderr, "reserve01 - done: %p, addr=%p, val=%p", addr, (void*)(*addr));
    }

  int
    reserve02(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, int instrs, int reads, int writes)
    {
      if (addr0 == addr1) {
        ++tx->num_dynamic_merges;
        return reserve01(tx, bitmask | (bitmask >> 1), addr0, instrs, reads, writes);
      }
      else
      {
        if (reserve01(tx, bitmask, addr0, instrs, reads, writes)) {
          return reserve01(tx, bitmask>>1, addr1, instrs, reads, writes);
        }
      }
      return 0;
    }

  int 
    reserve03(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, int instrs, int reads, int writes)
    {
      if (addr0 == addr1) {
        ++tx->num_dynamic_merges;
        if (bitmask & 1)
          bitmask = (bitmask >> 1) | 1;
        else
          bitmask = (bitmask >> 1);
        return reserve02(tx, bitmask, addr1, addr2, instrs, reads, writes);
      }
      else
      {
        if (reserve01(tx, bitmask, addr0, instrs, reads, writes)) {
          return reserve02(tx, bitmask>>1, addr1, addr2, instrs, reads, writes);
        }
      }
      return 0;
    }

  int
    reserve04(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, uintptr_t addr3, int instrs, int reads, int writes)
    {
      if (addr0 == addr1) {
        ++tx->num_dynamic_merges;
        if (bitmask & 1)
          bitmask = (bitmask >> 1) | 1;
        else
          bitmask = (bitmask >> 1);
        return reserve03(tx, bitmask, addr1, addr2, addr3, instrs, reads, writes);
      }
      else
      {
        if (reserve01(tx, bitmask, addr0, instrs, reads, writes)) {
          return reserve03(tx, bitmask>>1, addr1, addr2, addr3, instrs, reads, writes);
        }
      }
      return 0;
    }

  /**
   *  OrecEager rollback:
   *
   *    Run the redo log, possibly bump timestamp
   */
  template <class CM>
    stm::scope_t*
    OrecEager_Generic<CM>::rollback(STM_ROLLBACK_SIG(tx, upper_stack_bound, except, len))
    {
      // common rollback code
      PreRollback(tx);

      // run the undo log
      STM_UNDO(tx->undo_log, upper_stack_bound, except, len);

      // release the locks and bump version numbers by one... track the highest
      // version number we write, in case it is greater than timestamp.val
      uintptr_t max = 0;
      foreach (OrecList, j, tx->locks) {
        uintptr_t newver = (*j)->p + 1;
        (*j)->v.all = newver;
        max = (newver > max) ? newver : max;
      }
      // if we bumped a version number to higher than the timestamp, we need to
      // increment the timestamp to preserve the invariant that the timestamp
      // val is >= all orecs' values when unlocked
      uintptr_t ts = timestamp.val;
      if (max > ts)
        casptr(&timestamp.val, ts, (ts+1)); // assumes no transient failures

      // reset all lists
      tx->r_orecs.reset();
      tx->undo_log.reset();
      tx->locks.reset();

      // notify CM
      CM::onAbort(tx);

      // common unwind code when no pointer switching
      return PostRollback(tx);
    }

  /**
   *  OrecEager in-flight irrevocability:
   *
   *    Either commit the transaction or return false.  Note that we're already
   *    serial by the time this code runs.
   *
   *    NB: This doesn't Undo anything, so there's no need to protect the
   *        stack.
   */
  bool
    irrevoc(STM_IRREVOC_SIG(tx,))
    {
      // NB: This code is probably more expensive than it needs to be...

      // assume we're a writer, and increment the global timestamp
      uintptr_t end_time = 1 + faiptr(&timestamp.val);

      // skip validation only if nobody else committed
      if (end_time != (tx->start_time + 1)) {
        foreach (OrecList, i, tx->r_orecs) {
          // read this orec
          uintptr_t ivt = (*i)->v.all;
          // if unlocked and newer than start time, abort
          if ((ivt > tx->start_time) && (ivt != tx->my_lock.all))
            return false;
        }
      }

      // release locks
      foreach (OrecList, i, tx->locks)
        (*i)->v.all = end_time;

      // clean up
      tx->r_orecs.reset();
      tx->undo_log.reset();
      tx->locks.reset();
      return true;
    }

  /**
   *  OrecEager validation:
   *
   *    Make sure that all orecs that we've read have timestamps older than our
   *    start time, unless we locked those orecs.  If we locked the orec, we
   *    did so when the time was smaller than our start time, so we're sure to
   *    be OK.
   */
  void
    validate(TxThread* tx)
    {
      foreach (OrecList, i, tx->r_orecs) {
        // read this orec
        uintptr_t ivt = (*i)->v.all;
        // if unlocked and newer than start time, abort
        if ((ivt > tx->start_time) && (ivt != tx->my_lock.all))
          tx->tmabort(tx);
      }
    }

  /**
   *  Switch to OrecEager:
   *
   *    The timestamp must be >= the maximum value of any orec.  Some algs use
   *    timestamp as a zero-one mutex.  If they do, then they back up the
   *    timestamp first, in timestamp_max.
   */
  void
    onSwitchTo()
    {
      timestamp.val = MAXIMUM(timestamp.val, stm::timestamp_max.val);
    }
} // (anonymous namespace)

// -----------------------------------------------------------------------------
// Register initialization as declaratively as possible.
// -----------------------------------------------------------------------------
#define FOREACH_ORECEAGER(MACRO)                \
  MACRO(OrecEager, HyperAggressiveCM)         \
MACRO(OrecEagerHour, HourglassCM)           \
MACRO(OrecEagerBackoff, BackoffCM)          \
MACRO(OrecEagerHB, HourglassBackoffCM)

#define INIT_ORECEAGER(ID, CM)                          \
  template <>                                         \
void initTM<ID>() {                                 \
  OrecEager_Generic<stm::CM>::initialize(ID, #ID);    \
}

namespace stm {
  FOREACH_ORECEAGER(INIT_ORECEAGER)
}

#undef FOREACH_ORECEAGER
#undef INIT_ORECEAGER
