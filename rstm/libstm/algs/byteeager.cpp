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
 *  ByteEager Implementation
 *
 *    This is a good-faith implementation of the TLRW algorithm by Dice and
 *    Shavit, from SPAA 2010.  We use bytelocks, eager acquire, and in-place
 *    update, with timeout for deadlock avoidance.
 */

#include "../profiling.hpp"
#include "algs.hpp"

using stm::UNRECOVERABLE;
using stm::TxThread;
using stm::ByteLockList;
using stm::bytelock_t;
using stm::get_bytelock;
using stm::get_bytelock_elem;
using stm::get_bytelock_index;
using stm::UndoLogEntry;

#define TICKETS

#define STATS

#define RESERVE_ADDR(n, m) \
      write = bitmask & n; \
      index = get_bytelock_index((void **)m); \
      if (reserve(tx, write, index, numAddrs, upcomingInstructions, id)) { \
        if (tx->seq_num) { \
          tx->num_saved_log_entries += num_entries; \
          tx->tmabort(tx); \
        } else { \
          exp_backoff(tx); \
          continue; \
        } \
      } \
      if (write) { \
        ++num_entries; \
      }

#define LOG_ADDR(n, m) \
      if (bitmask & n) \
        tx->undo_log.insert(UndoLogEntry(STM_UNDO_LOG_ENTRY((void **)m, *((void **)m), mask)));

/**
 *  Declare the functions that we're going to implement, so that we can avoid
 *  circular dependencies.
 */
namespace {
  struct ByteEager
  {
    static TM_FASTCALL bool begin(TxThread*);
    static TM_FASTCALL void* read_ro(STM_READ_SIG(,,));
    static TM_FASTCALL void* read_rw(STM_READ_SIG(,,));
    static TM_FASTCALL void write_ro(STM_WRITE_SIG(,,,));
    static TM_FASTCALL void write_rw(STM_WRITE_SIG(,,,));
    static TM_FASTCALL void commit_ro(STM_COMMIT_SIG(,));
    static TM_FASTCALL void commit_rw(STM_COMMIT_SIG(,));
    static TM_FASTCALL int reserve_int(TxThread* tx, bool write, uintptr_t elem, int numAddrs, int upcomingInstructions, int id);
    static TM_FASTCALL int reserve(TxThread* tx, bool write, uintptr_t elem, int numAddrs, int upcomingInstructions, int id);
    static TM_FASTCALL uintptr_t reserverange(TxThread* tx, uintptr_t addr0, uintptr_t addr1);
    static TM_FASTCALL int releaserange(TxThread* tx, uintptr_t addr0, uintptr_t addr1);
    static TM_FASTCALL int reserve01(TxThread* tx, int bitmask, uintptr_t addr0, int numAddrs, int upcomingInstructions, int id);
    static TM_FASTCALL int reserve02(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, int numAddrs, int upcomingInstructions, int id);
    static TM_FASTCALL int reserve03(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, int numAddrs, int upcomingInstructions, int id);
    static TM_FASTCALL int reserve04(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, uintptr_t addr3, int numAddrs, int upcomingInstructions, int id);
    static TM_FASTCALL int reserve05(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, uintptr_t addr3, uintptr_t addr4, int numAddrs, int upcomingInstructions, int id);
    static TM_FASTCALL int reserve06(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, uintptr_t addr3, uintptr_t addr4, uintptr_t addr5, int numAddrs, int upcomingInstructions, int id);
    static TM_FASTCALL int reserve07(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, uintptr_t addr3, uintptr_t addr4, uintptr_t addr5, uintptr_t addr6, int numAddrs, int upcomingInstructions, int id);
    static TM_FASTCALL int reserveclear(TxThread* tx);


    static void logAbort(TxThread* tx, bool write, bool range, int type);
    static stm::scope_t* rollback(STM_ROLLBACK_SIG(,,,));
    static bool irrevoc(STM_IRREVOC_SIG(,));
    static void onSwitchTo();
  };

  /**
   *  These defines are for tuning backoff behavior
   */
#if defined(STM_CPU_SPARC)
#  define READ_TIMEOUT        32
#  define ACQUIRE_TIMEOUT     128
#  define DRAIN_TIMEOUT       1024
#else // STM_CPU_X86
#  define READ_TIMEOUT        32
#  define ACQUIRE_TIMEOUT     128
#  define DRAIN_TIMEOUT       4096
#endif

  /**
   *  ByteEager begin:
   */
  bool ByteEager::begin(TxThread* tx)
  {
    tx->started = true;
    tx->have_ticket = false;
    tx->partial_reserve = false;
    ++tx->tx_num;
    tx->seq_num = 0;
    tx->next_id = 0;
    assert(tx->range_bytelocks.size() == 0);
    tx->allocator.onTxBegin();
    return false;
  }

  void ByteEager::logAbort(TxThread* tx, bool write, bool range, int type)
  {
    int index = 6;
    if (tx->seq_num < 2) {
      index = 0;
    } else if (tx->seq_num < 4) {
      index = 1;
    } else if (tx->seq_num < 8) {
      index = 2;
    } else if (tx->seq_num < 16) {
      index = 3;
    } else if (tx->seq_num < 32) {
      index = 4;
    } else if (tx->seq_num < 64) {
      index = 5;
    }
    if (write) {
      if (range) {
        ++tx->seq_num_range[index];
      } else {
        ++tx->seq_num_w[index];
      }
    } else {
      ++tx->seq_num_r[index];
    }

    switch (type) {
      case 1:
        ++tx->num_read_aborts[index];
        break;
      case 2:
        ++tx->num_acquire_aborts[index];
        break;
      case 3:
        ++tx->num_drain_aborts[index];
        break;
    }

  }

  /**
   *  ByteEager commit (read-only):
   */
  void ByteEager::commit_ro(STM_COMMIT_SIG(tx,))
  {
    assert(!tx->have_ticket);
    
    // read-only... release read locks
    foreach (ByteLockList, i, tx->r_bytelocks)
      (*i)->reader[tx->id-1] = 0;

    tx->r_bytelocks.reset();
    tx->have_ticket = false;
#ifdef ALG_STATS
    tx->just_logged = 0;
#endif
    OnReadOnlyCommit(tx);
  }

  /**
   *  ByteEager commit (writing context):
   */
  void ByteEager::commit_rw(STM_COMMIT_SIG(tx,))
  {
    if (tx->have_ticket)
      assert(tx->w_bytelocks.size() == 0);
    // release write locks, then read locks
    foreach (ByteLockList, i, tx->range_bytelocks) {
      assert((*i)->owner == tx->id);
      if ((*i)->release_ownership()) {
        ++tx->range_dep_transfers;
      }
    }
    foreach (ByteLockList, i, tx->w_bytelocks) {
      if((*i)->owner == tx->id)
        (*i)->owner = 0;
    }
    foreach (ByteLockList, i, tx->r_bytelocks)
      (*i)->reader[tx->id-1] = 0;

    // clean-up
    tx->r_bytelocks.reset();
    tx->w_bytelocks.reset();
    tx->range_bytelocks.reset();
    tx->undo_log.reset();
    tx->have_ticket = false;
    OnReadWriteCommit(tx, read_ro, write_ro, commit_ro);
#ifdef ALG_STATS
    if (tx->just_logged)
      ++tx->num_skippable_undo_log_entries;
    tx->just_logged = 0;
#endif
  }

  /**
   *  ByteEager read (read-only transaction)
   */
  void* ByteEager::read_ro(STM_READ_SIG(tx,addr,))
  {
    uint32_t tries = 0;
    bytelock_t* lock = get_bytelock(addr);

    // do I have a read lock?
    if (lock->reader[tx->id-1] == 1)
      return *addr;

    // log this location
    tx->r_bytelocks.insert(lock);

    // now try to get a read lock
    while (true) {
      // mark my reader byte
      lock->set_read_byte(tx->id-1);

      // if nobody has the write lock, we're done
      if (__builtin_expect(lock->owner == 0, true))
        return *addr;

      // drop read lock, wait (with timeout) for lock release
      lock->reader[tx->id-1] = 0;
      while (lock->owner != 0) {
        if (++tries > READ_TIMEOUT)
          tx->tmabort(tx);
      }
    }
  }

  /**
   *  ByteEager read (writing transaction)
   */
  void* ByteEager::read_rw(STM_READ_SIG(tx,addr,))
  {
    uint32_t tries = 0;
    bytelock_t* lock = get_bytelock(addr);

    // do I have the write lock?
    if (lock->owner == tx->id)
      return *addr;

    // do I have a read lock?
    if (lock->reader[tx->id-1] == 1)
      return *addr;

    // log this location
    tx->r_bytelocks.insert(lock);

    // now try to get a read lock
    while (true) {
      // mark my reader byte
      lock->set_read_byte(tx->id-1);
      // if nobody has the write lock, we're done
      if (__builtin_expect(lock->owner == 0, true))
        return *addr;

      // drop read lock, wait (with timeout) for lock release
      lock->reader[tx->id-1] = 0;
      while (lock->owner != 0)
        if (++tries > READ_TIMEOUT)
          tx->tmabort(tx);
    }
  }

  /**
   *  ByteEager write (read-only context)
   */
  void ByteEager::write_ro(STM_WRITE_SIG(tx,addr,val,mask))
  {
    assert(!tx->have_ticket && !tx->partial_reserve);
    uint32_t tries = 0;
    bytelock_t* lock = get_bytelock(addr);

    // get the write lock, with timeout
    while (!bcas64(&(lock->owner), 0u, tx->id))
      if (++tries > ACQUIRE_TIMEOUT)
        tx->tmabort(tx);

    // log the lock, drop any read locks I have
    tx->w_bytelocks.insert(lock);
    lock->reader[tx->id-1] = 0;

    // wait (with timeout) for readers to drain out
    // (read 4 bytelocks at a time)
    volatile uint32_t* lock_alias = (volatile uint32_t*)&lock->reader[0];
    for (int i = 0; i < 16; ++i) {
      tries = 0;
      while (lock_alias[i] != 0)
        if (++tries > DRAIN_TIMEOUT)
          tx->tmabort(tx);
    }

    // add to undo log, do in-place write
    tx->undo_log.insert(UndoLogEntry(STM_UNDO_LOG_ENTRY(addr, *addr, mask)));
    STM_DO_MASKED_WRITE(addr, val, mask);

    OnFirstWrite(tx, read_rw, write_rw, commit_rw);
  }

  /**
   *  ByteEager write (writing context)
   */
  void ByteEager::write_rw(STM_WRITE_SIG(tx,addr,val,mask))
  {
    assert(!tx->have_ticket && !tx->partial_reserve);
    uint32_t tries = 0;
    bytelock_t* lock = get_bytelock(addr);

    // If I have the write lock, add to undo log, do write, return
    if (lock->owner == tx->id) {
      tx->undo_log.insert(UndoLogEntry(STM_UNDO_LOG_ENTRY(addr, *addr, mask)));
      STM_DO_MASKED_WRITE(addr, val, mask);
      return;
    }

    // get the write lock, with timeout
    while (!bcas64(&(lock->owner), 0u, tx->id))
      if (++tries > ACQUIRE_TIMEOUT)
        tx->tmabort(tx);

    // log the lock, drop any read locks I have
    tx->w_bytelocks.insert(lock);
    lock->reader[tx->id-1] = 0;

    // wait (with timeout) for readers to drain out
    // (read 4 bytelocks at a time)
    volatile uint32_t* lock_alias = (volatile uint32_t*)&lock->reader[0];
    for (int i = 0; i < 16; ++i) {
      tries = 0;
      while (lock_alias[i] != 0)
        if (++tries > DRAIN_TIMEOUT)
          tx->tmabort(tx);
    }

    // add to undo log, do in-place write
    tx->undo_log.insert(UndoLogEntry(STM_UNDO_LOG_ENTRY(addr, *addr, mask)));
    STM_DO_MASKED_WRITE(addr, val, mask);
  }

  int ByteEager::reserveclear(TxThread* tx)
  {
    assert(false);
    // release write locks, then read locks
    foreach (ByteLockList, i, tx->w_bytelocks)
      if ((*i)->owner == tx->id)
        (*i)->owner = 0;
    foreach (ByteLockList, i, tx->r_bytelocks)
      (*i)->reader[tx->id-1] = 0;

    // clean-up
    tx->r_bytelocks.reset();
    tx->w_bytelocks.reset();
    tx->undo_log.reset();
    return 0;
  }

  int ByteEager::reserve_int(TxThread* tx, bool write, uintptr_t index, int numAddrs, int upcomingInstructions, int id)
  {
#if 0
    bool over = false;

    if (bitmask >= 4)  {  
      bitmask -= 4;
      over = true;

      //fprintf(stderr, "XXX %d tx= %p, bitmask=%d, addr0=%p, val=%x\n", reads, tx, bitmask, addr0, (void*)*(long *)addr0);
    } else {
      //fprintf(stderr, "YYY %d tx= %p, bitmask=%d, addr0=%p, val=%x\n", reads, tx, bitmask, addr0, (void*)*(long *)addr0);
    }
#endif
    assert(tx->started);
    uint32_t tries = 0;
    bytelock_t* lock = get_bytelock_elem(index);

    if (!write) {
      // do I have the write lock?
      if (lock->owner == tx->id) {
        return 0;
      }

      // do I have a read lock?
      if (lock->reader[tx->id-1] == 1){
        return 0;
      }

      if (lock->has_count(tx->id)) {
        ++tx->range_dep_waits;
        while (lock->owner != tx->id) {
          ++tx->range_reserves_child_waits;
        }
        return 0;
      }

      assert(!tx->have_ticket && !tx->partial_reserve);

      // log this location
      tx->r_bytelocks.insert(lock);

      // now try to get a read lock
      while (true) {
        // mark my reader byte
        lock->set_read_byte(tx->id-1);

        // if nobody has the write lock, we're done
        if (__builtin_expect(lock->owner == 0, true)) {
          return 0;
        }

        if (lock->owner == tx->id) {
          return 0;
        }

        // drop read lock, wait (with timeout) for lock release
        lock->reader[tx->id-1] = 0;
        while (lock->owner != 0) {
          if (++tries > READ_TIMEOUT) {
            uint64_t owner = lock->owner;
            if (owner && lock->count[owner-1]) {
              ++tx->range_reserve_stranger_aborts;
            }
            return 1;
          }
        }
      }
    } else {
      // If I have the write lock, add to undo log, do write, return
      if (lock->owner == tx->id) {
        return 0;
      }

      if (lock->has_count(tx->id)) {
        ++tx->range_dep_waits;
        while (lock->owner != tx->id) {
          ++tx->range_reserves_child_waits;
        }
        return 0;
      }

      // get the write lock, with timeout
      while (!bcas64(&(lock->owner), 0u, tx->id)) {
        if (++tries > ACQUIRE_TIMEOUT) {
          uint64_t owner = lock->owner;
          if (owner && lock->count[owner-1]) {
            ++tx->range_reserve_stranger_aborts;
          }
          return 2;
        } 
      }

      assert(!tx->have_ticket && !tx->partial_reserve);

      // log the lock, drop any read locks I have
      unsigned long size = tx->w_bytelocks.insert(lock);
      lock->reader[tx->id-1] = 0;


      // wait (with timeout) for readers to drain out
      // (read 4 bytelocks at a time)
      volatile uint32_t* lock_alias = (volatile uint32_t*)&lock->reader[0];
      for (int i = 0; i < 16; ++i) {
        tries = 0;
        while (lock_alias[i] != 0)
          if (++tries > DRAIN_TIMEOUT) {
            //TODO: is this safe?
            //lock->owner = 0;
            //lock->reader[tx->id-1] = 0;
            //tx->w_bytelocks.reset();
            uint64_t owner = lock->owner;
            if (owner && lock->count[owner-1]) {
              ++tx->range_reserve_stranger_aborts;
            }
            return 3;
          }
      }

      // add to undo log, do in-place write
#ifdef ALG_STATS
      ++tx->num_undo_log_entries;

      if (writes == 0)
        ++tx->num_skipped_undo_log_entries;
#endif

      if (size == 1)
        OnFirstWrite(tx, read_rw, write_rw, commit_rw);
    }

    return 0; 
  }

  uintptr_t ByteEager::reserverange(TxThread* tx, uintptr_t addr0, uintptr_t addr1)
  {
    assert(!tx->have_ticket);
    ++tx->range_reserves;

    // First range reservation needs to acquire all locks
    for (uintptr_t addr = addr0; addr != addr1; addr += sizeof(void*)) {

      uintptr_t index = get_bytelock_index((void **)addr);
      /*if (index == stm::NUM_STRIPES) {
        index = 0;
        }*/

      uint32_t tries = 0;
      bytelock_t* lock = get_bytelock_elem(index);
      if (addr != addr0) {
        volatile uint32_t* lock_alias = (volatile uint32_t*)&lock->reader[0];
        for (int i = 0; i < 16; ++i) {
          if (lock_alias[i] != 0) {
            ++tx->range_reserve_reader_aborts;
            return addr;
          }
        }
      } else {
        tx->partial_reserve = true;
      }

      if (lock->owner == tx->id) {
        if(!lock->has_count(tx->id)) {
          tx->range_bytelocks.insert(lock);
        }
        lock->incr_reserve_byte(tx->id);
        continue;
      }

      if (tx->next_id) {
        while (lock->owner != tx->next_id) {}
        if(!lock->has_count(tx->id)) {
          tx->range_bytelocks.insert(lock);
        }
        lock->incr_reserve_byte(tx->id);
        continue;
      }

      // get the write lock, with timeout
      while (!bcas64(&(lock->owner), 0u, tx->id)) {
        if (lock->owner == tx->id) {
          break;
        }

        if (tx->next_id) {
          if (lock->owner == tx->next_id) {
            break;
          } else {
            ++tx->range_reserves_partial;
            return addr;
          }
        } else {
          uint32_t owner = lock->owner;
          if (owner) {
            if (lock->set_dep(owner, tx->id)) {
              tx->next_id = owner;

              ++tx->range_dep_reserves;
              break;             
            } else {
              ++tx->range_dep_reserve_fails;
              return addr;
            }
          }
        }
        /*
           if (++tries > ACQUIRE_TIMEOUT) {
           logAbort(tx, true, true, 2);
           assert(false);
           tx->tmabort(tx);
           } 
           */
      }
      lock->incr_reserve_byte(tx->id);

      //assert((lock->owner == tx->id) || (tx->next_id && (lock->owner == tx->next_id)));

      // log the lock, drop any read locks I have
      tx->range_bytelocks.insert(lock);
      lock->reader[tx->id-1] = 0;

      if (lock->owner == tx->id) {
        // wait (with timeout) for readers to drain out
        // (read 4 bytelocks at a time)
        volatile uint32_t* lock_alias = (volatile uint32_t*)&lock->reader[0];
        for (int i = 0; i < 16; ++i) {
          tries = 0;
          while (lock_alias[i] != 0) {
            ++tx->range_reserves_drain_waits;
            //         return addr;
            /*  
                if (++tries > DRAIN_TIMEOUT) {
                logAbort(tx, true, true, 3);
                assert(false);
                tx->tmabort(tx);
                }
                */
          }
        }
      }
    }

    foreach (ByteLockList, i, tx->w_bytelocks) {
      if (!(*i)->has_count(tx->id)) {
        assert((*i)->owner == tx->id);
        (*i)->owner = 0;
      }  
    }
    foreach (ByteLockList, i, tx->r_bytelocks) {
      if (!(*i)->has_count(tx->id)) {
        (*i)->reader[tx->id-1] = 0;
      }  
    }
    tx->r_bytelocks.reset();
    tx->w_bytelocks.reset();
    assert(tx->w_bytelocks.size() == 0);

    tx->have_ticket = true;
    return addr1;
  }

  int ByteEager::releaserange(TxThread* tx, uintptr_t addr0, uintptr_t addr1)
  {
    return 0;
  }

  int ByteEager::reserve(TxThread* tx, bool write, uintptr_t index, int numAddrs, int upcomingInstructions, int id)
  {
    int type = reserve_int(tx, write, index, numAddrs, upcomingInstructions, id);
    if (type) {
      if (tx->seq_num) {
#ifdef STATS
        logAbort(tx, write, false, type);
#endif
        return type;
      }

      ++tx->num_first_aborts[numAddrs-1];
      foreach (ByteLockList, i, tx->w_bytelocks)
        if ((*i)->owner == tx->id)
          (*i)->owner = 0;
      foreach (ByteLockList, i, tx->r_bytelocks)
        (*i)->reader[tx->id-1] = 0;

      // reset lists
      tx->r_bytelocks.reset();
      tx->w_bytelocks.reset();
      tx->undo_log.reset();

      // randomized exponential backoff
      // exp_backoff(tx);
    }

    return type;
  }

  int ByteEager::reserve01(TxThread* tx, int bitmask, uintptr_t addr0, int numAddrs, int upcomingInstructions, int id)
  {
#if 0
    foreach (ByteLockList, i, tx->r_bytelocks) {
      if (((*i)->owner != 0) && ((*i)->owner != tx->id))
        tx->tmabort(tx);
    }
#endif
    bool write;
    uintptr_t index;
    int num_entries;

    while (true) {
      num_entries = 0;

      RESERVE_ADDR(1, addr0);

      ++tx->seq_num;

      LOG_ADDR(1, addr0);

      return 1;
    }
  }

  int ByteEager::reserve02(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, int numAddrs, int upcomingInstructions, int id)
  {
    bool write;
    uintptr_t index;
    int num_entries;

    while (true) {
      num_entries = 0;

      RESERVE_ADDR(1, addr0);
      RESERVE_ADDR(2, addr1);

      ++tx->seq_num;

      LOG_ADDR(1, addr0);
      LOG_ADDR(2, addr1);

      return 1;
    }
  }

  int ByteEager::reserve03(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, int numAddrs, int upcomingInstructions, int id)
  {
    bool write;
    uintptr_t index;
    int num_entries;

    while (true) {
      num_entries = 0;

      RESERVE_ADDR(1, addr0);
      RESERVE_ADDR(2, addr1);
      RESERVE_ADDR(4, addr2);

      ++tx->seq_num;

      LOG_ADDR(1, addr0);
      LOG_ADDR(2, addr1);
      LOG_ADDR(4, addr2);

      return 1;
    }
  }

  int ByteEager::reserve04(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, uintptr_t addr3, int numAddrs, int upcomingInstructions, int id)
  {
    bool write;
    uintptr_t index;
    int num_entries;

    while (true) {
      num_entries = 0;

      RESERVE_ADDR(1, addr0);
      RESERVE_ADDR(2, addr1);
      RESERVE_ADDR(4, addr2);
      RESERVE_ADDR(8, addr3);

      ++tx->seq_num;

      LOG_ADDR(1, addr0);
      LOG_ADDR(2, addr1);
      LOG_ADDR(4, addr2);
      LOG_ADDR(8, addr3);

      return 1;
    }
  }

  int ByteEager::reserve05(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, uintptr_t addr3, uintptr_t addr4, int numAddrs, int upcomingInstructions, int id)
  {
    bool write;
    uintptr_t index;
    int num_entries;

    while (true) {
      num_entries = 0;

      RESERVE_ADDR(1, addr0);
      RESERVE_ADDR(2, addr1);
      RESERVE_ADDR(4, addr2);
      RESERVE_ADDR(8, addr3);
      RESERVE_ADDR(16, addr4);

      ++tx->seq_num;

      LOG_ADDR(1, addr0);
      LOG_ADDR(2, addr1);
      LOG_ADDR(4, addr2);
      LOG_ADDR(8, addr3);
      LOG_ADDR(16, addr4);

      return 1;
    }
  }

  int ByteEager::reserve06(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, uintptr_t addr3, uintptr_t addr4, uintptr_t addr5, int numAddrs, int upcomingInstructions, int id)
  {
    bool write;
    uintptr_t index;
    int num_entries;

    while (true) {
      num_entries = 0;

      RESERVE_ADDR(1, addr0);
      RESERVE_ADDR(2, addr1);
      RESERVE_ADDR(4, addr2);
      RESERVE_ADDR(8, addr3);
      RESERVE_ADDR(16, addr4);
      RESERVE_ADDR(32, addr5);

      ++tx->seq_num;

      LOG_ADDR(1, addr0);
      LOG_ADDR(2, addr1);
      LOG_ADDR(4, addr2);
      LOG_ADDR(8, addr3);
      LOG_ADDR(16, addr4);
      LOG_ADDR(32, addr5);

      return 1;
    }
  }

  int ByteEager::reserve07(TxThread* tx, int bitmask, uintptr_t addr0, uintptr_t addr1, uintptr_t addr2, uintptr_t addr3, uintptr_t addr4, uintptr_t addr5, uintptr_t addr6, int numAddrs, int upcomingInstructions, int id)
  {
    bool write;
    uintptr_t index;
    int num_entries;

    while (true) {
      num_entries = 0;

      RESERVE_ADDR(1, addr0);
      RESERVE_ADDR(2, addr1);
      RESERVE_ADDR(4, addr2);
      RESERVE_ADDR(8, addr3);
      RESERVE_ADDR(16, addr4);
      RESERVE_ADDR(32, addr5);
      RESERVE_ADDR(64, addr6);

      ++tx->seq_num;

      LOG_ADDR(1, addr0);
      LOG_ADDR(2, addr1);
      LOG_ADDR(4, addr2);
      LOG_ADDR(8, addr3);
      LOG_ADDR(16, addr4);
      LOG_ADDR(32, addr5);
      LOG_ADDR(64, addr6);

      return 1;
    }
  }

  /**
   *  ByteEager unwinder:
   */
  stm::scope_t* ByteEager::rollback(STM_ROLLBACK_SIG(tx, upper_stack_bound, except, len))
  {
    assert(!tx->have_ticket);
    assert(!tx->partial_reserve);
    PreRollback(tx);

    // Undo the writes, while at the same time watching out for the exception
    // object.
    STM_UNDO(tx->undo_log, upper_stack_bound, except, len);

    // release write locks, then read locks
    foreach (ByteLockList, i, tx->w_bytelocks)
      if ((*i)->owner == tx->id)
        (*i)->owner = 0;
    foreach (ByteLockList, i, tx->r_bytelocks)
      (*i)->reader[tx->id-1] = 0;

    // reset lists
    tx->r_bytelocks.reset();
    tx->w_bytelocks.reset();
    tx->undo_log.reset();
    tx->have_ticket = false;

    // randomized exponential backoff
    exp_backoff(tx);

    return PostRollback(tx, read_ro, write_ro, commit_ro);
  }

  /**
   *  ByteEager in-flight irrevocability:
   */
  bool ByteEager::irrevoc(STM_IRREVOC_SIG(,))
  {
    return false;
  }

  /**
   *  Switch to ByteEager:
   */
  void ByteEager::onSwitchTo() {
  }
}

namespace stm {
  /**
   *  ByteEager initialization
   */
  template<>
    void initTM<ByteEager>()
    {
      // set the name
      stms[ByteEager].name      = "ByteEager";

      // set the pointers
      stms[ByteEager].begin     = ::ByteEager::begin;
      stms[ByteEager].commit    = ::ByteEager::commit_ro;
      stms[ByteEager].read      = ::ByteEager::read_ro;
      stms[ByteEager].write     = ::ByteEager::write_ro;
      stms[ByteEager].reserverange = ::ByteEager::reserverange;
      stms[ByteEager].releaserange = ::ByteEager::releaserange;
      stms[ByteEager].reserve01 = ::ByteEager::reserve01;
      stms[ByteEager].reserve02 = ::ByteEager::reserve02;
      stms[ByteEager].reserve03 = ::ByteEager::reserve03;
      stms[ByteEager].reserve04 = ::ByteEager::reserve04;
      stms[ByteEager].reserve05 = ::ByteEager::reserve05;
      stms[ByteEager].reserve06 = ::ByteEager::reserve06;
      stms[ByteEager].reserve07 = ::ByteEager::reserve07;
      stms[ByteEager].rollback  = ::ByteEager::rollback;
      stms[ByteEager].reserveclear = ::ByteEager::reserveclear;
      stms[ByteEager].irrevoc   = ::ByteEager::irrevoc;
      stms[ByteEager].switcher  = ::ByteEager::onSwitchTo;
      stms[ByteEager].privatization_safe = true;
    }
}
