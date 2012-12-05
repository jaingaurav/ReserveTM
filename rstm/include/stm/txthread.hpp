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
 *  Definitions for a common environment for all our STM implementations.
 *  The TxThread object holds all the metadata that a thread needs.
 *
 *  In addition, this file declares the thread-local pointer that a thread
 *  can use to access its TxThread object.
 */

#ifndef TXTHREAD_HPP__
#define TXTHREAD_HPP__

#include "alt-license/rand_r_32.h"
#include "common/locks.hpp"
#include "common/ThreadLocal.hpp"
#include "stm/metadata.hpp"
#include "stm/WriteSet.hpp"
#include "stm/UndoLog.hpp"
#include "stm/ValueList.hpp"
#include "WBMMPolicy.hpp"
#include <set>

#define RESERVES_ACTIVE 1
//#define STATS_ACTIVE 1

namespace stm
{
  /**
   *  The TxThread struct holds all of the metadata that a thread needs in
   *  order to use any of the STM algorithms we support.  In the past, this
   *  class also had all global STM metadata as static fields, and had lots
   *  of methods to support the various STM implementations.  This proved to
   *  be too cumbersome for some compilers, so we now use this simpler
   *  interface.  This file can be included in application code without
   *  pulling in an obscene amount of STM-related function definitions.
   *
   *  Unfortunately, we still have to pull in metadata.hpp :(
   *
   *  NB: the order of fields has not been rigorously studied.  It is very
   *      likely that a better order would improve performance.
   */
  struct TxThread
  {
      /*** THESE FIELDS DEAL WITH THE STM IMPLEMENTATIONS ***/
      uint64_t       id;            // per thread id
      uint32_t       nesting_depth; // nesting; 0 == not in transaction
      WBMMPolicy     allocator;     // buffer malloc/free
      uint32_t       num_commits;   // stats counter: commits
      uint32_t       num_aborts;    // stats counter: aborts
      uint32_t       num_restarts;  // stats counter: restart()s
      uint32_t       num_ro;        // stats counter: read-only commits

      std::set<void *> reserved_reads;
      std::set<void *> reserved_writes;
      std::set<void *> read_set;
      std::set<void *> write_set;
      uint32_t       num_reserved_calls;
      uint32_t       num_reserved_reads;
      uint32_t       num_reserved_writes;
      uint32_t       num_non_reserved_reads;
      uint32_t       num_non_reserved_writes;
      uint32_t       num_redundant_reserved_reads;
      uint32_t       num_redundant_reserved_reads_from_writes;
      uint32_t       num_redundant_reserved_writes;
      uint32_t       num_redundant_non_reserved_reads;
      uint32_t       num_redundant_non_reserved_writes;
      uint32_t       num_duplicate_non_reserved_reads;
      uint32_t       num_duplicate_non_reserved_writes;
      uint32_t num_writer_stalls;
      uint32_t num_writer_stall_loops;
uint32_t num_undo_log_entries;
uint32_t num_skippable_undo_log_entries;
uint32_t just_logged;    
uint32_t num_skipped_undo_log_entries;
uint32_t num_dynamic_merges;
uint32_t num_reserve_aborts[4];
public:
bool started;
scope_t* volatile scope;      // used to roll back; also flag for isTxnl
      uintptr_t      start_time;    // start time of transaction
      uintptr_t      end_time;      // end time of transaction
      uintptr_t      ts_cache;      // last validation time
      bool           tmlHasLock;    // is tml thread holding the lock
      UndoLog        undo_log;      // etee undo log
      ValueList      vlist;         // NOrec read log
      WriteSet       writes;        // write set
      OrecList       r_orecs;       // read set for orec STMs
      OrecList       locks;         // list of all locks held by tx
      id_version_t   my_lock;       // lock word for orec STMs
      filter_t*      wf;            // write filter
      filter_t*      rf;            // read filter
      volatile uint32_t prio;       // for priority
      uint32_t       consec_aborts; // count consec aborts
      uint32_t       seed;          // for randomized backoff
      RRecList       myRRecs;       // indices of rrecs I set
      intptr_t       order;         // for stms that order txns eagerly
      volatile uint32_t alive;      // for STMs that allow remote abort
      ByteLockList   r_bytelocks;   // list of all byte locks held for read
      ByteLockList   w_bytelocks;   // all byte locks held for write
      BitLockList    r_bitlocks;    // list of all bit locks held for read
      BitLockList    w_bitlocks;    // list of all bit locks held for write
      mcs_qnode_t*   my_mcslock;    // for MCS
      uintptr_t      valid_ts;      // the validation timestamp for each tx
      uintptr_t      cm_ts;         // the contention manager timestamp
      filter_t*      cf;            // conflict filter (RingALA)
      NanorecList    nanorecs;      // list of nanorecs held
      uint32_t       consec_commits;// count consec commits
      toxic_t        abort_hist;    // for counting poison
      uint32_t       begin_wait;    // how long did last tx block at begin
      bool           strong_HG;     // for strong hourglass
      bool           irrevocable;   // tells begin_blocker that I'm THE ONE

      /*** PER-THREAD FIELDS FOR ENABLING ADAPTIVITY POLICIES */
      uint64_t      end_txn_time;      // end of non-transactional work
      uint64_t      total_nontxn_time; // time on non-transactional work

      /*** POINTERS TO INSTRUMENTATION */

      /**
       *  The read/write/commit instrumentation is reached via per-thread
       *  function pointers, which can be exchanged easily during execution.
       *
       *  The begin function is not a per-thread pointer, and thus we can use
       *  it for synchronization.  This necessitates it being volatile.
       *
       *  The other function pointers can be overwritten by remote threads,
       *  but that the synchronization when using the begin() function avoids
       *  the need for those pointers to be volatile.
       */

      /**
       * The global pointer for starting transactions. The return value should
       * be true if the transaction was started as irrevocable, the caller can
       * use this return to execute completely uninstrumented code if it's
       * available.
       */
      static TM_FASTCALL bool(*volatile tmbegin)(TxThread*);

      private:
      /*** Per-thread commit, read, and write pointers */
      TM_FASTCALL void(*tmcommit)(STM_COMMIT_SIG(,));
      TM_FASTCALL void*(*tmread)(STM_READ_SIG(,,));
      TM_FASTCALL void(*tmwrite)(STM_WRITE_SIG(,,,));
      TM_FASTCALL void(*tmreserverange)(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, int size, int instrs, int reads, int writes);
      TM_FASTCALL void(*tmreserve01)(TxThread* tx, int bitmask, uintptr_t addr0, int instrs, int reads, int writes);
      TM_FASTCALL void(*tmreserve02)(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, int instrs, int reads, int writes);
      TM_FASTCALL void(*tmreserve03)(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, int instrs, int reads, int writes);
      TM_FASTCALL void(*tmreserve04)(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, uintptr_t addr3, int instrs, int reads, int writes);

      public:
      /**
       * Some APIs, in particular the itm API at the moment, want to be able
       * to rollback the top level of nesting without actually unwinding the
       * stack. Rollback behavior changes per-implementation (some, such as
       * CGL, can't rollback) so we add it here.
       */
      static scope_t* (*tmrollback)(STM_ROLLBACK_SIG(,,,));

      /**
       * The function for aborting a transaction. The "tmabort" function is
       * designed as a configurable function pointer so that an API environment
       * like the itm shim can override the conflict abort behavior of the
       * system. tmabort is configured using sys_init.
       *
       * Some advanced APIs may not want a NORETURN abort function, but the stm
       * library at the moment only handles this option.
       */
      static NORETURN void (*tmabort)(TxThread*);

      /*** how to become irrevocable in-flight */
      static bool(*tmirrevoc)(STM_IRREVOC_SIG(,));

      /**
       * for shutting down threads.  Currently a no-op.
       */
      static void thread_shutdown() { }

      /**
       * the init factory.  Construction of TxThread objects is only possible
       * through this function.  Note, too, that destruction is forbidden.
       */
      static void thread_init();


      TM_FASTCALL void commit()
      {
#if STATS_ACTIVE
          reserved_reads.clear();
          reserved_writes.clear();
          read_set.clear();
          write_set.clear();
#endif
started = false;
          tmcommit(this);
      }
      TM_FASTCALL void* read(void** addr)
      {
#if STATS_ACTIVE
          ++num_non_reserved_reads;
          std::set<void *>::iterator it = reserved_reads.find(addr);
          if (it != reserved_reads.end())
          {
              ++num_redundant_non_reserved_reads;
          }
          else
          {
              it = reserved_writes.find(addr);
              if (it != reserved_writes.end())
              {
                  ++num_redundant_non_reserved_reads;
              }
              /*
              else
              {
                  it = write_set.find(addr);
                  if (it != write_set.end())
                  {
                      ++num_duplicate_non_reserved_reads;
                  }
              }*/
          }

          std::pair<std::set<void *>::iterator,bool> ret = read_set.insert(addr);
          if (ret.second==false)
              ++num_duplicate_non_reserved_reads;
#endif
          return tmread(this,addr);
      }

      TM_FASTCALL void write(void** addr, void* val)
      {
#if STATS_ACTIVE
          ++num_non_reserved_writes;
          std::set<void *>::iterator it = reserved_writes.find(addr);
          if (it != reserved_writes.end())
          {
              ++num_redundant_non_reserved_writes;
          }
              std::pair<std::set<void *>::iterator,bool> ret = write_set.insert(addr);
              if (ret.second==false)
                  ++num_duplicate_non_reserved_writes;
#endif
          tmwrite(this,addr,val);
      }

      void reserveRead( void* addr )
      {
          ++num_reserved_reads;
          std::set<void *>::iterator it = reserved_writes.find(addr);
          if (it != reserved_writes.end())
          {
              ++num_redundant_reserved_reads_from_writes;
          }
              std::pair<std::set<void *>::iterator,bool> ret = reserved_reads.insert(addr);
              if (ret.second==false)
                  ++num_redundant_reserved_reads;
      }

      void reserveWrite( void* addr )
      {
          ++num_reserved_writes;
          std::pair<std::set<void *>::iterator,bool> ret = reserved_writes.insert(addr);
          if (ret.second==false)
              ++num_redundant_reserved_writes;
      }

      TM_FASTCALL void reserverange(int bitmask, uintptr_t addr0, uintptr_t addr1, int size, int instrs, int reads, int writes)
      {
#if STATS_ACTIVE
          ++num_reserved_calls;
          if (bitmask & (1 << 0)) {
              reserveWrite((void*)addr0);
          } else {
              reserveRead((void*)addr0);
          }
#endif
#if RESERVES_ACTIVE
          tmreserverange(this, bitmask, addr0, addr1, size, instrs, reads, writes);
#endif
      }

      TM_FASTCALL void reserve01(int bitmask, uintptr_t addr0, int instrs, int reads, int writes)
      {
#if STATS_ACTIVE
          ++num_reserved_calls;
          if (bitmask & (1 << 0)) {
              reserveWrite((void*)addr0);
          } else {
              reserveRead((void*)addr0);
          }
#endif
#if RESERVES_ACTIVE
          tmreserve01(this, bitmask, addr0, instrs, reads, writes);
#endif
      }

      TM_FASTCALL void reserve02(int bitmask, uintptr_t addr0, uintptr_t addr1, int instrs, int reads, int writes)
      {
#if STATS_ACTIVE
          ++num_reserved_calls;
          if (bitmask & (1 << 0)) {
              reserveWrite((void*)addr0);
          } else {
              reserveRead((void*)addr0);
          }
          if (bitmask & (1 << 1)) {
              reserveWrite((void*)addr1);
          } else {
              reserveRead((void*)addr1);
          }
#endif
#if RESERVES_ACTIVE
          tmreserve02(this, bitmask, addr0, addr1, instrs, reads, writes);
#endif
      }

      TM_FASTCALL void reserve03(int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, int instrs, int reads, int writes)
      {
#if STATS_ACTIVE
          ++num_reserved_calls;
          if (bitmask & (1 << 0)) {
              reserveWrite((void*)addr0);
          } else {
              reserveRead((void*)addr0);
          }
          if (bitmask & (1 << 1)) {
              reserveWrite((void*)addr1);
          } else {
              reserveRead((void*)addr1);
          }
          if (bitmask & (1 << 2)) {
              reserveWrite((void*)addr2);
          } else {
              reserveRead((void*)addr2);
          }
#endif
#if RESERVES_ACTIVE
          tmreserve03(this, bitmask, addr0, addr1, addr2, instrs, reads, writes);
#endif
      }

      TM_FASTCALL void reserve04(int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, uintptr_t addr3, int instrs, int reads, int writes)
      {
#if STATS_ACTIVE
          ++num_reserved_calls;
          if (bitmask & (1 << 0)) {
              reserveWrite((void*)addr0);
          } else {
              reserveRead((void*)addr0);
          }
          if (bitmask & (1 << 1)) {
              reserveWrite((void*)addr1);
          } else {
              reserveRead((void*)addr1);
          }
          if (bitmask & (1 << 2)) {
              reserveWrite((void*)addr2);
          } else {
              reserveRead((void*)addr2);
          }
          if (bitmask & (1 << 3)) {
              reserveWrite((void*)addr3);
          } else {
              reserveRead((void*)addr3);
          }
#endif
#if RESERVES_ACTIVE
          tmreserve04(this, bitmask, addr0, addr1, addr2, addr3, instrs, reads, writes);
#endif
      }

      bool checkReadFunc(TM_FASTCALL void*(*readFunc)(STM_READ_SIG(,,)))
      {
          return (tmread == readFunc);
      }

      void setReadWriteCommit(
      TM_FASTCALL void*(*readFunc)(STM_READ_SIG(,,)),
      TM_FASTCALL void(*writeFunc)(STM_WRITE_SIG(,,,)), TM_FASTCALL void(*commitFunc)(STM_COMMIT_SIG(,)))
      {
          tmread = readFunc;
          tmwrite = writeFunc;
          tmcommit = commitFunc;
      }

      void setReserve(
          TM_FASTCALL void(*reserverange)(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, int size, int instrs, int reads, int writes),
          TM_FASTCALL void(*reserve01)(TxThread* tx, int bitmask, uintptr_t addr0, int instrs, int reads, int writes),
      TM_FASTCALL void(*reserve02)(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, int instrs, int reads, int writes),
      TM_FASTCALL void(*reserve03)(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, int instrs, int reads, int writes),
      TM_FASTCALL void(*reserve04)(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, uintptr_t addr3, int instrs, int reads, int writes))
      {
          tmreserverange = reserverange;
          tmreserve01 = reserve01;
          tmreserve02 = reserve02;
          tmreserve03 = reserve03;
          tmreserve04 = reserve04;
      }
    protected:
      TxThread();
      ~TxThread() { }
  }; // class TxThread

  /*** GLOBAL VARIABLES RELATED TO THREAD MANAGEMENT */
  extern THREAD_LOCAL_DECL_TYPE(TxThread*) Self; // this thread's TxThread

} // namespace stm

#endif // TXTHREAD_HPP__
