#ifndef LLVM_ANALYSIS_RESERVETM_ALIASMAPPER_H
#define LLVM_ANALYSIS_RESERVETM_ALIASMAPPER_H

#include <map>
#include <set>

namespace llvm {
    class Value;
    class BasicBlock;
    class GetElementPtrInst;
    class Function;
    class CallInst;
    class Module;
    class Instruction;
}

namespace ReserveTM {
#ifndef LLVM_ANALYSIS_ReserveTM_VALUESET
    typedef std::set<llvm::Value *> ValueSet;
#define LLVM_ANALYSIS_ReserveTM_VALUESET
#endif
    typedef std::set<llvm::Instruction *> InstructionSet;
    typedef std::set<llvm::BasicBlock *> BasicBlockSet;
    typedef std::set<llvm::Function *> FunctionSet;

    class AliasMapperRelation {
        public:
            AliasMapperRelation(llvm::Value * m) : me(m), fLoadedFrom(0), fOffsetParent(0), fOffsetParentOffset(0) { }
            //private:
            llvm::Value * me;
            ValueSet fAliases;
            ValueSet fLoadedBy;
            llvm::Value * fLoadedFrom;
            ValueSet fStoredInto;
            ValueSet fStoredFrom;
            llvm::Value * fOffsetParent;
            llvm::GetElementPtrInst * fOffsetParentOffset;
            std::multimap<llvm::GetElementPtrInst *, llvm::Value *> fOffsetChildren;
            bool getAliases(ValueSet& aliases, std::set<AliasMapperRelation *>& visited, std::set<AliasMapperRelation *>& errors);
    };

    class AliasMapper {
        public:
            static void analyzeModule(llvm::Module &M);
            static AliasMapperRelation* getAliasSet(llvm::Value *a);
            static ValueSet getPeers(llvm::Value* v); 
            static bool getAliases(llvm::Value *v, ValueSet& aliases);
            static void aliasValues(llvm::Value *a, llvm::Value* b);
        private:
            static std::multimap<llvm::Function *, llvm::CallInst *> fFunctionCallSites;
            static void analyzeBlock(llvm::BasicBlock *const block);
            static void aliasOffsetValues(llvm::Value *parent, llvm::Value* child, llvm::GetElementPtrInst * gep);
            static void aliasLoad(llvm::Value* src, llvm::Value* dst);
            static void aliasStore(llvm::Value* src, llvm::Value* dst);
    };
}

#endif
