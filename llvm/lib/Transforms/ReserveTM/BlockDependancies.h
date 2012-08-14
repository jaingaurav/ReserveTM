#ifndef LLVM_ANALYSIS_RESERVETM_BLOCK_DEPENDANCIES_H
#define LLVM_ANALYSIS_RESERVETM_BLOCK_DEPENDANCIES_H

namespace llvm {
    class Value;
    class PHINode;
}

namespace ReserveTM {
#ifndef LLVM_ANALYSIS_ReserveTM_VALUESET
    typedef std::set<llvm::Value *> ValueSet;
#define LLVM_ANALYSIS_ReserveTM_VALUESET
#endif
    class BlockDependancies {
        private:
            std::map<llvm::Value*, unsigned> allocs;
            std::map<llvm::Value*, unsigned> frees;
            std::map<llvm::Value*, unsigned> loads;
            std::map<llvm::Value*, unsigned> stores;
            std::set<llvm::PHINode*> phi_loads;
            std::set<llvm::PHINode*> phi_stores;
            ValueSet prev_loads;
            ValueSet prev_stores;
            std::vector<llvm::Value*> ordered_loads_stores;
            unsigned currentIndex;
            uint32_t fBitVector;
            bool fUpcomingWrite;

        public:
            BlockDependancies() : currentIndex(0), fBitVector(0), fUpcomingWrite(false) { }
            ~BlockDependancies() {
                //TODO
                //assert(loads.empty());
                //assert(stores.empty());
                //assert(ordered_loads_stores.empty());
            }
            bool empty(); 
            size_t size(); 
            bool containsLoadFrom(llvm::Value *v); 
            bool containsStoreTo(llvm::Value *v);
            llvm::Value* containsLoadFrom(ValueSet &values);
            llvm::Value* containsStoreTo(ValueSet &values);
            bool canCompressLoadPhiNode(llvm::PHINode* phiNode, ValueSet &prev_loads, ValueSet &prev_stores);
            bool canCompressStorePhiNode(llvm::PHINode* phiNode, ValueSet &prev_loads, ValueSet &prev_stores);
            void compressPhiNodes();
            bool insertLoad(llvm::Value *v);
            bool insertStore(llvm::Value *v);
            bool insertAlloc(llvm::Value *v);
            bool insertFree(llvm::Value *v);
            bool compressWithPreviousLoad(llvm::Value* v);
            bool compressWithPreviousStore(llvm::Value* v);
            void compress(ValueSet &prev_loads, ValueSet &prev_stores);
            unsigned numOrderedLoadsStores();
            uint32_t copyLoadsStores(llvm::Value ** v);
            void copyLoads(ValueSet &s);
            void copyStores(ValueSet &s);
            unsigned numLoads();
            unsigned numStores();
            bool setUpcomingWrite() { bool old = fUpcomingWrite; fUpcomingWrite = true; return old; }
            bool upcomingWrite() { return fUpcomingWrite; }
            bool hasStore() { return !(stores.empty() && allocs.empty() && frees.empty()); }
            void debugPrint();
    };
}

#endif
