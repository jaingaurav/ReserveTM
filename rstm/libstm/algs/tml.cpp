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
 *  TML Implementation
 *
 *    This STM was published by Dalessandro et al. at EuroPar 2010.  The
 *    algorithm allows multiple readers or a single irrevocable writer.  The
 *    semantics are at least as strong as ALA.
 *
 *    NB: now that we dropped the inlined-tml instrumentation hack, we should
 *        probably add ro/rw functions
 */

#include "../profiling.hpp"
#include "algs.hpp"
#include "tml_inline.hpp"
#include <stm/UndoLog.hpp> // STM_DO_MASKED_WRITE

using stm::TxThread;
using stm::timestamp;
using stm::Trigger;
using stm::UNRECOVERABLE;


/**
 *  Declare the functions that we're going to implement, so that we can avoid
 *  circular dependencies.  Note that with TML, we don't expect the reads and
 *  writes to be called, because we expect the instrumentation to be inlined
 *  via the dispatch mechanism.  However, we must provide the code to handle
 *  the uncommon case.
 */
namespace {
  struct TML {
      static TM_FASTCALL bool begin(TxThread*);
      static TM_FASTCALL void* read(STM_READ_SIG(,,));
      static TM_FASTCALL void write(STM_WRITE_SIG(,,,));
      static TM_FASTCALL void commit(STM_COMMIT_SIG(,));
      static TM_FASTCALL void reserve01(TxThread* tx, int bitmask, uintptr_t addr0, int instrs, int reads, int writes);
      static TM_FASTCALL void reserve02(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, int instrs, int reads, int writes);
      static TM_FASTCALL void reserve03(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, int instrs, int reads, int writes);
      static TM_FASTCALL void reserve04(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, uintptr_t addr3, int instrs, int reads, int writes);

      static stm::scope_t* rollback(STM_ROLLBACK_SIG(,,,));
      static bool irrevoc(STM_IRREVOC_SIG(,));
      static void onSwitchTo();
  };

  /**
   *  TML begin:
   */
  bool
  TML::begin(TxThread* tx)
  {
      int counter = 0;
      // Sample the sequence lock until it is even (unheld)
      while ((tx->start_time = timestamp.val) & 1) {
          spin64();
          counter += 64;
      }

      uintptr_t val;
      do {
          val = stm::num_active_readers.val;
      } while (!bcasptr(&stm::num_active_readers.val, val, val + 1));

      // notify the allocator
      tx->begin_wait = counter;
      tx->allocator.onTxBegin();
      return false;
  }

  /**
   *  TML commit:
   */
  void
  TML::commit(STM_COMMIT_SIG(tx,))
  {
      // writing context: release lock, free memory, remember commit
      if (tx->tmlHasLock) {
          ++timestamp.val;
          tx->tmlHasLock = false;
          OnReadWriteCommit(tx);
      }
      // reading context: just remember the commit
      else {
          uintptr_t val;
          do {
              val = stm::num_active_readers.val;
          } while (!bcasptr(&stm::num_active_readers.val, val, val - 1));
          OnReadOnlyCommit(tx);
      }
      Trigger::onCommitLock(tx);
  }

  /**
   *  TML read:
   *
   *    If we have the lock, we're irrevocable so just do a read.  Otherwise,
   *    after doing the read, make sure we are still valid.
   */
  void*
  TML::read(STM_READ_SIG(tx,addr,))
  {
      void* val = *addr;
      if (tx->tmlHasLock)
          return val;
      // NB:  afterread_tml includes a CFENCE
      afterread_TML(tx);
      return val;
  }

  /**
   *  TML write:
   *
   *    If we have the lock, do an in-place write and return.  Otherwise, we
   *    need to become irrevocable first, then do the write.
   */
  void
  TML::write(STM_WRITE_SIG(tx,addr,val,mask))
  {
      if (tx->tmlHasLock) {
          STM_DO_MASKED_WRITE(addr, val, mask);
          return;
      }
      // NB:  beforewrite_tml includes a fence via CAS
      beforewrite_TML(tx);
      STM_DO_MASKED_WRITE(addr, val, mask);
  }

  void
  TML::reserve01(TxThread* tx, int bitmask, uintptr_t addr0, int instrs, int reads, int writes)
  {
      if (!tx->tmlHasLock) {
          uintptr_t val;
          //only reads
          if (!bitmask) {
              // If it's a reader check if it needs to abort
              CFENCE;
              if (__builtin_expect(timestamp.val != tx->start_time, false)) {
#ifdef ALG_STATS
		      if (writes == 0)
             ++tx->num_skipped_undo_log_entries;
#endif
/*                  do {
                      val = stm::num_active_readers.val;
                  } while (!bcasptr(&stm::num_active_readers.val, val, val - 1));*/
                  tx->tmabort(tx);
              }
          } else {
              // No longer a reader
              // acquire the lock, abort on failure
              if (!bcasptr(&timestamp.val, tx->start_time, tx->start_time + 1)) {
                  tx->tmabort(tx);
	      }
              do {
                  val = stm::num_active_readers.val;
              } while (!bcasptr(&stm::num_active_readers.val, val, val - 1));
              ++tx->start_time;
              tx->tmlHasLock = true;
              //Wait till all the readers have left
              int counter = 0;
#ifdef ALG_STATS
              if (stm::num_active_readers.val != 0)
                  ++tx->num_writer_stalls;
#endif
	      while (stm::num_active_readers.val != 0) {
                  spin64();
                  counter += 64;
#ifdef ALG_STATS
                  ++tx->num_writer_stall_loops;
#endif
	      }
          }
      }
  }

  void
  TML::reserve02(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, int instrs, int reads, int writes)
  {
      reserve01(tx, bitmask, addr0, instrs, reads, writes);
  }

  void
  TML::reserve03(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, int instrs, int reads, int writes)
  {
      reserve02(tx, bitmask, addr0, addr1, instrs, reads, writes);
  }
  
  void
  TML::reserve04(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, uintptr_t addr3, int instrs, int reads, int writes)
  {
      reserve03(tx, bitmask, addr0, addr1, addr2, instrs, reads, writes);
  }

  /**
   *  TML unwinder
   *
   *    NB: This should not be called from a writing context!  That means
   *        calling restart() under TML with writes is not allowed, but we
   *        don't currently enforce.
   *
   *    NB: don't need to worry about exception object since anyone rolling
   *        back must be read-only, and thus the logs have no writes to
   *        exception objects pending.
   */
  stm::scope_t*
  TML::rollback(STM_ROLLBACK_SIG(tx,,,))
  {
          uintptr_t val;
                        do {
                      val = stm::num_active_readers.val;
                  } while (!bcasptr(&stm::num_active_readers.val, val, val - 1));
      PreRollback(tx);
      return PostRollback(tx);
  }

  /**
   *  TML in-flight irrevocability:
   *
   *    We have a custom path for going irrevocable in TML, so this code should
   *    never be called.
   */
  bool
  TML::irrevoc(STM_IRREVOC_SIG(,))
  {
      UNRECOVERABLE("IRREVOC_TML SHOULD NEVER BE CALLED");
      return false;
  }

  /**
   *  Switch to TML:
   *
   *    We just need to be sure that the timestamp is not odd, or else we will
   *    block.  For safety, increment the timestamp to make it even, in the
   *    event that it is odd.
   */
  void
  TML::onSwitchTo()
  {
      if (timestamp.val & 1)
          ++timestamp.val;
  }
} // (anonymous namespace)

namespace stm {
  template<>
  void initTM<TML>()
  {
      // set the name
      stms[TML].name      = "TML";

      // set the pointers
      stms[TML].begin     = ::TML::begin;
      stms[TML].commit    = ::TML::commit;
      stms[TML].read      = ::TML::read;
      stms[TML].write     = ::TML::write;
      stms[TML].reserve01 = ::TML::reserve01;
      stms[TML].reserve02 = ::TML::reserve02;
      stms[TML].reserve03 = ::TML::reserve03;
      stms[TML].reserve04 = ::TML::reserve04;
      stms[TML].rollback  = ::TML::rollback;
      stms[TML].irrevoc   = ::TML::irrevoc;
      stms[TML].switcher  = ::TML::onSwitchTo;
      stms[TML].privatization_safe = true;
  }
}
