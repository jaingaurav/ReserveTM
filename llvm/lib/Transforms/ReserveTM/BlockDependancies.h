#ifndef LLVM_ANALYSIS_RESERVETM_BLOCK_DEPENDANCIES_H
#define LLVM_ANALYSIS_RESERVETM_BLOCK_DEPENDANCIES_H

namespace llvm {
  class Value;
  class PHINode;
  class Instruction;
}

namespace ReserveTM {
#ifndef LLVM_ANALYSIS_ReserveTM_VALUESET
  typedef std::set<llvm::Value *> ValueSet;
#define LLVM_ANALYSIS_ReserveTM_VALUESET
#endif
  class ReservationSite {
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
      uint32_t fUpcomingReads;
      uint32_t fUpcomingWrites;
      uint32_t fUpcomingInstructions;
      bool fOverIntrumentation;

    public:
      llvm::Instruction* Instr;
      llvm::Value* tx;
      llvm::Value* Val;
      typedef enum {
        LOAD,
        STORE,
        ALLOC,
        FREE
      } Type;
      Type Ty;
      ReservationSite(llvm::Instruction *I, llvm::Value *V, Type T, bool OverInstrumentation = false);
      ~ReservationSite();
      bool empty(); 
      size_t size();
      llvm::Value* getValue();
      Type getType();
      bool containsLoadFrom(llvm::Value *v); 
      bool containsStoreTo(llvm::Value *v);
      llvm::Value* containsLoadFrom(ValueSet &values);
      llvm::Value* containsStoreTo(ValueSet &values);
      bool canCompressLoadPhiNode(llvm::PHINode* phiNode, ValueSet &prev_loads, ValueSet &prev_stores);
      bool canCompressStorePhiNode(llvm::PHINode* phiNode, ValueSet &prev_loads, ValueSet &prev_stores);
      void compressPhiNodes();
      bool insertLoad(llvm::Value *v, bool over = false);
      bool insertStore(llvm::Value *v, bool over = false);
      bool insertAlloc(llvm::Value *v);
      bool insertFree(llvm::Value *v);
      bool compressWithPreviousLoad(llvm::Value* v);
      bool compressWithPreviousStore(llvm::Value* v);
      void compress(ValueSet &prev_loads, ValueSet &prev_stores);
      unsigned numOrderedLoadsStores();
      uint32_t copyLoadsStores(llvm::Value ** v);
      void copyLoads(ValueSet &s);
      void copyStores(ValueSet &s);
      unsigned numReads();
      unsigned numWrites();
      unsigned numLoads();
      unsigned numStores();
      void setUpcomingReads(uint32_t reads) { fUpcomingReads = reads; }
      uint32_t upcomingReads() { return fUpcomingReads; }
      void setUpcomingWrites(uint32_t writes) { fUpcomingWrites = writes; }
      uint32_t upcomingWrites() { return fUpcomingWrites; }
      void setUpcomingInstructions(uint32_t instrs) { fUpcomingInstructions = instrs; }
      uint32_t upcomingInstructions() { return fUpcomingInstructions; }
      bool hasStore() { return !(stores.empty() && allocs.empty() && frees.empty()); }
      void debugPrint();
  };
}

#endif
