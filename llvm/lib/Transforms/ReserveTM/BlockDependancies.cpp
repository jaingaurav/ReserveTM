#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Instructions.h"
#include "llvm/Constants.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/LLVMContext.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ValueSymbolTable.h"
#include "llvm/Support/Casting.h"
#include <map>
#include <queue>
#include <vector>
#include <set>
#include <algorithm>
#include <stack>

#include "BlockDependancies.h"

using namespace llvm;
using ReserveTM::ValueSet;

STATISTIC(num_loads_on_phi,                             "4.2.1  Loads on PHI values (total)");
STATISTIC(num_loads_on_phi_compressed,                  "4.2.3  Loads on PHI values compressed");
STATISTIC(num_loads_skipped,                            "4.5    Loads skipped (duplicate)");
STATISTIC(num_loads_skipped_from_previous_store,        "4.6    Loads skipped from previous store");

STATISTIC(num_stores_on_phi,                            "5.3    Stores on PHI values(total)");
STATISTIC(num_stores_on_phi_compressed,                 "5.4    Stores on PHI values compressed");
STATISTIC(num_stores_skipped,                           "5.5    Stores skipped (total)");

bool ReserveTM::BlockDependancies::empty() {
    return loads.empty() && stores.empty() && allocs.empty() && frees.empty();
}

size_t ReserveTM::BlockDependancies::size() {
    return loads.size() + stores.size();
}


bool ReserveTM::BlockDependancies::containsLoadFrom(Value *v) {
    if (loads.find(v) == loads.end()) {
        return false;
    }

    return true;
}

bool ReserveTM::BlockDependancies::containsStoreTo(Value *v) {
    if (stores.find(v) == stores.end()) {
        if (allocs.find(v) == allocs.end()) {
            if (frees.find(v) == frees.end()) {
                return false;
            }
        }
    }

    return true;
}

Value* ReserveTM::BlockDependancies::containsLoadFrom(ValueSet &values) {
    for (auto v : values) {
        if (containsLoadFrom(v))
            return v;
    }

    return 0;
}

Value* ReserveTM::BlockDependancies::containsStoreTo(ValueSet &values) {
    for (auto v : values) {
        if (containsStoreTo(v))
            return v;
    }

    return 0;
}

bool ReserveTM::BlockDependancies::canCompressLoadPhiNode(PHINode* phiNode, ValueSet &prev_loads, ValueSet &prev_stores) {
    for (unsigned int i = 0; i < phiNode->getNumIncomingValues(); ++i) {
        Value *v = phiNode->getIncomingValue(i);
        if (isa<PHINode>(v)) {
            if (!canCompressLoadPhiNode(phiNode, prev_loads, prev_stores))
                return false;
        } else if (prev_stores.find(v) != prev_stores.end()) {
            continue;
        } else if (prev_loads.find(v) != prev_loads.end()) {
            continue;
        } else if (stores.find(v) != stores.end()) {
            continue;
        } else if (loads.find(v) != loads.end()) {
            continue;
        } else {
            return false;
        }
    }
    return true;
}

bool ReserveTM::BlockDependancies::canCompressStorePhiNode(PHINode* phiNode, ValueSet &prev_loads, ValueSet &prev_stores) {
    for (unsigned int i = 0; i < phiNode->getNumIncomingValues(); ++i) {
        Value *v = phiNode->getIncomingValue(i);
        if (isa<PHINode>(v)) {
            if (!canCompressStorePhiNode(phiNode, prev_loads, prev_stores))
                return false;
        } else if (prev_stores.find(v) != prev_stores.end()) {
            continue;
        } else if (stores.find(v) != stores.end()) {
            continue;
        } else {
            return false;
        }
    }
    return true;
}

void ReserveTM::BlockDependancies::compressPhiNodes() {
    for (auto phiNode : phi_loads) {
        if (canCompressLoadPhiNode(phiNode, prev_loads, prev_stores)) {
            ++num_loads_on_phi_compressed;

            auto phi_it = loads.find(phiNode);
            if (phi_it != loads.end())
                loads.erase(phi_it);
        }
    }

    for (auto phiNode : phi_stores) {
        if (canCompressStorePhiNode(phiNode, prev_loads, prev_stores)) {
            ++num_stores_on_phi_compressed;

            auto phi_it = stores.find(phiNode);
            if (phi_it != stores.end())
                stores.erase(phi_it);
        }
    }
}

bool ReserveTM::BlockDependancies::insertLoad(Value *v) {
    if (PHINode* phiNode = dyn_cast<PHINode>(v)) {
        ++num_loads_on_phi;
        if (phi_stores.find(phiNode) == phi_stores.end()) {
            phi_loads.insert(phiNode);
        }
    }

    if (stores.find(v) != stores.end()) {
        ++num_loads_skipped_from_previous_store;
    } else {
        if (loads.find(v) != loads.end()) {
            ++num_loads_skipped;
        } else {
            loads.insert(std::pair<Value*, unsigned>(v, currentIndex));
            ordered_loads_stores.push_back(v);
            ++currentIndex;

            assert(currentIndex < 32);
        }
    }
}

bool ReserveTM::BlockDependancies::insertStore(Value *v) {
    if (PHINode* phiNode = dyn_cast<PHINode>(v)) {
        ++num_stores_on_phi;
        phi_stores.insert(phiNode);
    }

    if (stores.find(v) != stores.end()) {
        ++num_stores_skipped;
    } else {
        stores.insert(std::pair<Value*, unsigned>(v, currentIndex));
        ordered_loads_stores.push_back(v);
        assert(currentIndex < 32);
        fBitVector |= (1 << currentIndex);
        ++currentIndex;
    }
}

bool ReserveTM::BlockDependancies::insertAlloc(Value *v) {
    assert(!isa<PHINode>(v));
    //TODO: avoid re-ordering

    allocs.insert(std::pair<Value*, unsigned>(v, 0));
}

bool ReserveTM::BlockDependancies::insertFree(Value *v) {
    assert(!isa<PHINode>(v));
    //TODO: avoid re-ordering

    frees.insert(std::pair<Value*, unsigned>(v, 0));
}

unsigned ReserveTM::BlockDependancies::numOrderedLoadsStores() {
    unsigned count = 0;
    for (auto entry : ordered_loads_stores) {
        if (entry != 0) {
            ++count;
        }
    }
    return count;
}

uint32_t ReserveTM::BlockDependancies::copyLoadsStores(Value ** v) {
    uint32_t bit_vector = 0;
    unsigned index = 0;
    unsigned index2 = 0;
    for (auto val : ordered_loads_stores) {
        if (val != 0) {
            *v = val;
            ++v;
            if (fBitVector & (1 << index)) {
                bit_vector |= (1 << index2);
            }
            ++index2;
        }
        ++index;
    }

    return bit_vector;
}

void ReserveTM::BlockDependancies::copyLoads(ValueSet &s) {
    for (auto it : loads) {
        s.insert(it.first);
    }
}
void ReserveTM::BlockDependancies::copyStores(ValueSet &s) {
    for (auto it : stores) {
        s.insert(it.first);
    }
}

unsigned ReserveTM::BlockDependancies::numLoads() {
    return loads.size();
}

unsigned ReserveTM::BlockDependancies::numStores() {
    return stores.size();
}

void ReserveTM::BlockDependancies::debugPrint() {
    errs() << loads.size() << " loads and " << stores.size() << " stores." << "\n";
    /*
       if (!loads.empty()) {
       errs() << "Load Set: ";
       for (auto it : loads) {
       printVal(it.first);
       errs() << " ";
       }
       errs() << "\n";
       }

       if (!stores.empty()) {
       errs() << "Stores Set: ";
       for (auto it : stores) {
       printVal(it.first);
       errs() << " ";
       }
       errs() << "\n";
       }
       */
}

bool ReserveTM::BlockDependancies::compressWithPreviousLoad(Value* v) {
    prev_loads.insert(v);
    auto loads_it = loads.find(v);
    if (loads_it != loads.end()) {
        ordered_loads_stores[loads_it->second] = 0;
        loads.erase(loads_it);
        return true;
    }
    return false;
}

bool ReserveTM::BlockDependancies::compressWithPreviousStore(Value* v) {
    prev_stores.insert(v);
    bool retVal = false;

    if (compressWithPreviousLoad(v)) {
        retVal = true;
    }

    auto stores_it = stores.find(v);
    if (stores_it != stores.end()) {
        ordered_loads_stores[stores_it->second] = 0;
        stores.erase(stores_it);
        retVal = true;
    }

    return retVal;
}

void ReserveTM::BlockDependancies::compress(ValueSet &prev_loads, ValueSet &prev_stores) {
    for (auto loads_it = prev_loads.begin(), loads_it_e = prev_loads.end(); loads_it != loads_it_e; ++loads_it)
        compressWithPreviousLoad(*loads_it);

    for (auto stores_it = prev_stores.begin(), stores_it_e = prev_stores.end(); stores_it != stores_it_e; ++stores_it )
        compressWithPreviousStore(*stores_it);
}

