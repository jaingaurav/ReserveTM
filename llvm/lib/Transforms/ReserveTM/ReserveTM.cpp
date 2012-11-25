#define DEBUG_TYPE "ReserveTM"
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

#include "AliasMapper.h"
#include "BlockDependancies.h"

using namespace llvm;
using ReserveTM::ValueSet;

#define DEBUG_INFO 1
//#define ELIMINATE_FIRST

STATISTIC(num_instructions_analyzed,                    "1.1    Instructions analyzed");
STATISTIC(num_loads,                                    "1.2.1  Loads (total)");
STATISTIC(num_loads_from_stm_call,                      "1.2.2  Loads from stm calls");
STATISTIC(num_stores,                                   "1.3.1  Stores (total)");
STATISTIC(num_stores_from_stm_call,                     "1.3.2  Stores from stm calls");
STATISTIC(num_allocs,                                   "1.4.1  Allocs (total)");
STATISTIC(num_allocs_from_stm_call,                     "1.4.2  Allocs from stm calls");
STATISTIC(num_frees,                                    "1.5.1  Frees (total)");
STATISTIC(num_frees_from_stm_call,                      "1.5.2  Frees from stm calls");
STATISTIC(num_skipped_tm_calls,                         "1.6    Skipped TM calls");

STATISTIC(num_reservation_sites,                        "2.1    Reservation sites");
STATISTIC(num_reservation_sites_partially_compressed,   "2.2.1  Reservation sites partially compressed");
STATISTIC(num_reservation_sites_completely_compressed,  "2.2.2  Reservation sites completely compressed");
STATISTIC(num_reservation_sites_partially_eliminated,   "2.3.1  Reservation sites partially eliminated");
STATISTIC(num_reservation_sites_completely_eliminated,  "2.3.2  Reservation sites completely eliminated");
STATISTIC(num_reservation_sites_partially_merged,       "2.4.1  Reservation sites partially merged");
STATISTIC(num_reservation_sites_completely_merged,      "2.4.2  Reservation sites completely merged");
STATISTIC(num_reservation_sites_instrumented,           "2.5    Reservation sites instrumented");
STATISTIC(num_reservation_sites_skipped,                "2.5    Reservation sites skipped");
STATISTIC(num_reservation_sites_with_upcoming_write,    "2.6    Reservation sites with upcoming write");
STATISTIC(num_reservation_sites_at_end,                 "2.7    Reservation sites at end");
STATISTIC(num_reservation_sites_followed_by_loop,       "2.8    Reservation sites followed by loop");
STATISTIC(num_reservation_sites_with_previous_store,    "2.9    Reservation sites with previous store");

STATISTIC(num_functions,                                "3.1    Functions analyzed"); 
STATISTIC(num_functions_with_memory_dependancies,       "3.2    Functions with memory dependencies"); 
STATISTIC(num_functions_instrumented,                   "3.3    Functions instrumented");
STATISTIC(num_functions_pointer_calls,                  "3.4    Functions pointer calls");

STATISTIC(num_stm_reserve_1,                            "4.1    STM reservations with 1 entry");
STATISTIC(num_stm_reserve_2,                            "4.2    STM reservations with 2 entries");
STATISTIC(num_stm_reserve_3,                            "4.3    STM reservations with 3 entries");
STATISTIC(num_stm_reserve_4,                            "4.4    STM reservations with 4 entries");

STATISTIC(num_loads_compressed,                         "5.1.1  Loads compressed");
STATISTIC(num_loads_compressed_inter_procedurally,      "5.1.2  Loads compressed inter-procedurally");
STATISTIC(num_loads_compressed_thread_local,            "5.1.3  Loads compressed thread local");
STATISTIC(num_loads_eliminated_thread_local,            "5.1.3  Loads eliminated thread local");
STATISTIC(num_loads_eliminated_thread_local_whole,      "5.1.4  Loads eliminated thread local (whole)");
STATISTIC(num_loads_merged,                             "5.2.1  Loads merged");
STATISTIC(num_loads_merged_inter_procedurally,          "5.2.2  Loads merged inter-procedurally");
STATISTIC(num_loads_eliminated,                         "5.3    Loads Eliminated");

STATISTIC(num_stores_compressed,                        "6.1.1  Stores compressed");
STATISTIC(num_stores_compressed_inter_procedurally,     "6.1.2  Stores compressed inter-procedurally");
STATISTIC(num_stores_compressed_thread_local,           "6.1.3  Stores compressed thread local");
STATISTIC(num_stores_eliminated_thread_local,           "6.1.3  Stores eliminated thread local");
STATISTIC(num_stores_merged,                            "6.2.1  Stores merged");
STATISTIC(num_stores_merged_inter_procedurally,         "6.2.2  Stores merged inter-procedurally");

bool printAliasEliminate = false;
bool compress = true;
bool eliminate = true;
bool strongIsolation = true;
bool merge = true;
bool singleWriter = true;
bool fullInstrumentation = true;
bool replaceInstrumentation = false;

namespace {

    typedef std::set<Function *> FunctionSet;

    void printValues(ValueSet &values);
    void printVal(Value *v); 
    void printInst(Instruction *I, bool var = false); 
    bool functionIsValid(Function *func);
}

namespace ReserveTM {
    // ReserveTM::ReserveTMPass - The first implementation, without getAnalysisUsage.
    struct ReserveTMPass : public ModulePass {
        static char ID; // Pass identification, replacement for typeid
        ReserveTMPass();
        ~ReserveTMPass();

        bool analyzeFunction(Function * const function, InstructionSet& analyzedInstructions, std::queue<Function *>& funcQueue, InstructionSet& functionPointerBlocks);
        void getAnalyzedInstructions(Function * const function, InstructionSet& analyzedInstructions);
        InstructionSet fAnalyzedInstructions;

        typedef std::map<Instruction *, BlockDependancies*> InstructionMap;
        InstructionMap fReservationSiteMap;

        enum CompressionResult
        {
            FAIL,
            SUCCESS_INTER_PROCEDURAL,
            SUCCESS_INTRA_PROCEDURAL,
        };

        bool eliminateLoads(InstructionMap::const_iterator entry, ValueSet& cachedEliminations, ValueSet& cachedNonEliminations);
        bool willReserveValue(BasicBlock* block, ValueSet values, bool store, InstructionSet& visited );
        bool willReserveValue(Instruction* instr, ValueSet values, bool store, InstructionSet& visited );
        bool willReserveValue(CallInst* ci, ValueSet values, bool store, InstructionSet& visited );
        CompressionResult canCompressValue(Instruction *instr, ValueSet values, bool store, InstructionSet& visited, bool skip = false, bool initial = false);
        void compressBlockValues(InstructionMap::const_iterator entry, bool stores);
        bool compressBlock(InstructionMap::const_iterator entry);
        void mergeValue(Instruction *instr, Value* v, bool store, std::queue<InstructionMap::const_iterator>& mergeQueue);
        CompressionResult canMergeValue(Instruction *instr, Value* v, InstructionSet& visited, bool initial = false);
        bool mergeBlock(InstructionMap::const_iterator entry, std::queue<InstructionMap::const_iterator>& mergeQueue);

bool calcReadsWrites(CallInst* ci, uint32_t* instrs, uint32_t* reads, uint32_t* writes, InstructionSet& visited);
bool calcReadsWrites(Instruction* instr, uint32_t* instrs, uint32_t* reads, uint32_t* writes, InstructionSet& visited);
bool calcReadsWrites(BasicBlock* block, uint32_t* instrs, uint32_t* reads, uint32_t* writes, InstructionSet& visited, Instruction* start = NULL);

std::multimap<Function *, CallInst *> fFunctionCallSites;
        std::set<CallInst*> fFunctionCalls;
        InstructionSet fFunctionPointerBlocks;
        BasicBlockSet fCompressedBlocks;
        std::queue<Function *> fFunctionPointerQueue;


        bool isFromAlloc(Value *v) {
            if (Instruction *I = dyn_cast<Instruction>(v)) {
                if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(I)) {
                    return isFromAlloc(gep->getPointerOperand());
              //  } else if (PtrToIntInst *pt = dyn_cast<PtrToIntInst>(I)) {
                    //TODO: be more rigorous
                //    return isFromAlloc(pt->getOperand(0));
                } else if (BitCastInst *bc = dyn_cast<BitCastInst>(I)) {
                    //TODO: be more rigorous
                    return isFromAlloc(bc->getOperand(0));
                } else if (CallInst *ci = dyn_cast<CallInst>(I)) {
                 /*   auto func = ci->getCalledFunction();
                    if (func && func->hasName() && ((func->getName().str().find("malloc") != std::string::npos) || (func->getName().str().find("tx_alloc") != std::string::npos))) {
                        return true;
                    }*/
                } else if (isa<AllocaInst>(I)) {
                    return true;
                }
                return false;
            } else if (Argument *arg = dyn_cast<Argument>(v)) {
                Function *func = arg->getParent();
                auto ret = fFunctionCallSites.equal_range(func);
                for (auto callSiteIt=ret.first; callSiteIt!=ret.second; ++callSiteIt) {
                    auto ci = (*callSiteIt).second;
                    if (!isFromAlloc(ci->getArgOperand(arg->getArgNo())))
                        return false;
                }
                return true;
            }

            return false;
        }


        Instruction * getFirstInstruction(Function * func) {
            return &*func->getEntryBlock().begin();
        }

        std::set<Instruction*> getPrevious(Instruction* I) {
            std::set<Instruction*> prev;
            auto block = I->getParent();
            if (I == block->begin()) {
                if (pred_begin(block) == pred_end(block)) {
                    auto func = block->getParent();
                    assert(&func->getEntryBlock() == block);
                    auto ret = fFunctionCallSites.equal_range(func);
                    for (auto callSiteIt=ret.first; callSiteIt!=ret.second; ++callSiteIt) {
                        prev.insert((*callSiteIt).second);
                    }
                } else {
                    for (pred_iterator pi = pred_begin(block), pi_e = pred_end(block); pi != pi_e; ++pi) {
                        BasicBlock *pred = *pi;

                        assert(pred->size());

                        auto instr_e = pred->end();
                        prev.insert(--instr_e);
                    }
                }
            } else {
                for (auto instr_i = block->begin(), instr_e = block->end(); instr_i != instr_e; ++instr_i) {
                    if (&*instr_i == I) {
                        prev.insert(--instr_i);
                        break;
                    }
                }
            }

            return prev;
        }

	std::set<Instruction*> getPrevious(Function * func) {
return getPrevious(getFirstInstruction(func));
	}

        std::set<Function*> getCalledFunctions(CallInst* ci) {
            std::set<Function*> funcs;

            //TODO: handle function pointers
            auto func = ci->getCalledFunction();
            if (func && functionIsValid(func)) {
                funcs.insert(func);
            }

            return funcs;
        }

        virtual bool runOnModule(Module &M);
        virtual void getAnalysisUsage(AnalysisUsage &AU) const {
            //BasicBlockPass::getAnalysisUsage(AU);
            //AU.addRequired<AliasAnalysis>();
            //AU.addPreserved<AliasAnalysis>();
        }

        Function* stm_reserve[4];
        FunctionSet fTxFunctions;
    };
}

char ReserveTM::ReserveTMPass::ID = 0;
#if 1
static RegisterPass<ReserveTM::ReserveTMPass> X("ReserveTM", "ReserveTM World Pass");
#else
static const char ReserveTM::ReserveTMPass_name[] = "ReserveTM::ReserveTMPass World Pass";
INITIALIZE_PASS_BEGIN(ReserveTM::ReserveTMPass, "ReserveTM::ReserveTMPass", ReserveTM::ReserveTMPass_name, false, false)
INITIALIZE_AG_DEPENDENCY(AliasAnalysis)
    INITIALIZE_PASS_END(ReserveTM::ReserveTMPass, "ReserveTM::ReserveTMPass", ReserveTM::ReserveTMPass_name, false, false)
#endif

    namespace {
        void printValues(ValueSet &values) {
            for (auto v : values) {
                errs() << *v << "\n";
            }
        }

        void printVal(Value *v) {
            errs() << "Defining (";
            if (Instruction *I  = dyn_cast<Instruction>(v)) {
                printInst(I);
            } else if (isa<Argument>(v)) {
                errs() << "Function Argument";
            } else {
                errs() << "NOPE";
            }
            errs() << ")";
            const Type* type = v->getType();
            if (type->isIntegerTy()) {
                errs() << "Integer" << type->getIntegerBitWidth() << "(";
                if (ConstantInt  *ci = dyn_cast<ConstantInt>(&*v)) {
                    errs() << ci->getZExtValue();
                }
            } else if (type->isPointerTy()) {
                errs() << "Pointer(";
                errs().write_escaped(v->getName());
            } else if (type->isFunctionTy()) {
                errs() << "Function(";
                errs().write_escaped(v->getName());
            } else {
                errs() << "Unknown(";
            }
            errs() << ")";
        }

        void printInst(Instruction *I, bool var) {
            if (LoadInst *li = dyn_cast<LoadInst>(I)) {
                errs() << "LoadInst";
                if (var) {
                    errs() << " ";
                    printVal(li->getPointerOperand());
                }
            } else if (isa<AllocaInst>(I)) {
                errs() << "AllocaInst";
            } else if (isa<ReturnInst>(I)) {
                errs() << "ReturnInst"; 
            } else if (StoreInst *si = dyn_cast<StoreInst>(I)) {
                errs() << "StoreInst";
                if (var) {
                    errs() << " ";
                    printVal(si->getValueOperand());
                    errs() << " ";
                    printVal(si->getPointerOperand());
                }
            } else if (isa<GetElementPtrInst>(I)) {
                errs() << "GetElementPtrInst";
            } else  if (CallInst *ci = dyn_cast<CallInst>(I)) {
                errs() << "CallInst: ";
                Function* called = ci->getCalledFunction();
                if (called && !called->isIntrinsic()) {
                    errs().write_escaped(called->getName());
                } else {
                    errs() << "*NONE*";
                }
                if (var) {
                    errs() << " (" << ci->getNumArgOperands() << " args) ";
                    for (unsigned arg_num = 0; arg_num < ci->getNumArgOperands(); ++arg_num) {
                        errs() << arg_num << ": ";
                        printVal(ci->getArgOperand(arg_num));
                        errs() << " ";
                    }
                }
            } else if (isa<BinaryOperator>(I)) {
                errs() << "BinaryOperator";
            } else if (isa<UnaryInstruction>(I)) {
                errs() << "UnaryInstruction";
            } else if (isa<SelectInst>(I)) {
                errs() << "SelectInst";
            } else if (isa<TerminatorInst>(I)) {
                errs() << "TerminatorInst";
            } else if (isa<PHINode>(I)) {
                errs() << "PHINode";
            } else {
                errs() << "Unknown";
            }
        }

        bool functionIsValid(Function *func) {
            if (!func->isIntrinsic()
                && func->hasName()
                && (func->getName().str().find("_ZN3stm") == std::string::npos)
                && (func->getName().str().find("free") == std::string::npos)
                && (func->getName().str().find("abs") == std::string::npos)
                && (func->getName().str().find("printf") == std::string::npos)
                && (func->getName().str().find("puts") == std::string::npos)
                && (func->getName().str().find("fwrite") == std::string::npos)
                && (func->getName().str().find("acos") == std::string::npos)
                && (func->getName().str().find("sqrt") == std::string::npos)
                && (func->getName().str().find("malloc") == std::string::npos)
                && (func->getName().str().find("_assert") == std::string::npos)
                && (func->getName().str().find("pthread") == std::string::npos)) {
                return true;
            }

            return false;
        }

    }

ReserveTM::ReserveTMPass::ReserveTMPass() : ModulePass(ID) {
    for (int i = 0; i < 4; ++i) {
        stm_reserve[i] = 0;
    }
}
ReserveTM::ReserveTMPass::~ReserveTMPass() {
}

bool ReserveTM::ReserveTMPass::analyzeFunction(Function * const function,
    InstructionSet& analyzedInstructions,
    std::queue<Function *>& funcQueue,
    InstructionSet& functionPointerBlocks) {
    DEBUG_WITH_TYPE("analyze", errs() << "Analyzing Function: " << function << " size: " << function->size() << "\n");

    bool memory_dependancies = false;
    auto ls = new BlockDependancies();
    for (inst_iterator instr_i = inst_begin(function), E = inst_end(function); instr_i != E; ) {
        Instruction *I = &*instr_i;
        DEBUG_WITH_TYPE("analyze", errs() << "Instr: (" << I << ") ");
        DEBUG_WITH_TYPE("analyze", printInst(I, true));
        DEBUG_WITH_TYPE("analyze", errs() << "\n");

       if (analyzedInstructions.find(I) != analyzedInstructions.end())
           return false;
        if (!ls)
            ls = new BlockDependancies();

        analyzedInstructions.insert(I);

        if (LoadInst *li = dyn_cast<LoadInst>(I)) {
            ++num_loads;
         //   if (fullInstrumentation)
           //     ls->insertLoad(li->getPointerOperand(), true);
        } else if (StoreInst *si = dyn_cast<StoreInst>(I)) {
            ++num_stores;
            //if (fullInstrumentation)
              //  ls->insertStore(si->getPointerOperand(), true);
        } else if (CallInst *ci = dyn_cast<CallInst>(I)) {
            Function* called = ci->getCalledFunction();
            if (!called || !called->isIntrinsic()) {
                if (called
                    && called->hasName()
                    && ((called->getName().str().find("stm_read") != std::string::npos)
                        || (called->getName().str().find("stm_write") != std::string::npos)
                        || (called->getName().str().find("tx_alloc") != std::string::npos)
                        || (called->getName().str().find("tx_free") != std::string::npos))) {
                    if (called->getName().str().find("tx_alloc") != std::string::npos) {
                        ++num_allocs;
                        ++num_allocs_from_stm_call;
                        ls->insertAlloc(ci);
                    } else {
                        Value *arg = ci->getArgOperand(0);
                      /*  if (Constant *c = dyn_cast<Constant>(arg)) {
                            if (c->isNullValue()) {
                                //continue;
                            }
                            ++num_skipped_tm_calls;
                        }
		       	else if (arg->getType()->isPointerTy())
			*/
			{
                            if (called->getName().str().find("stm_read") != std::string::npos) {
                                ++num_loads_from_stm_call;
#if 1
if (replaceInstrumentation) {
                                Instruction *newI = new LoadInst(arg, "newRead", true);
                                ReplaceInstWithInst(ci, newI);
                                instr_i = inst_begin(function);
                                while (&*instr_i != newI) {
                                    ++instr_i;
                                }
                                continue;
} else {
                                ++num_loads;
                                ls->insertLoad(arg);
}
#endif
                            } else if (called->getName().str().find("stm_write") != std::string::npos) {
                                ++num_stores_from_stm_call;
#if 1
if (replaceInstrumentation) {
                                Instruction *newI = new StoreInst(ci->getArgOperand(1), arg, "newWrite", true);
                                ReplaceInstWithInst(ci, newI);
                                instr_i = inst_begin(function);
                                while (&*instr_i != newI) {
                                    ++instr_i;
                                }
                                continue;
} else {
                                ++num_stores;
                                ls->insertStore(arg);
}
#endif
                            } else if (called->getName().str().find("tx_free") != std::string::npos) {
                                ++num_frees;
                                ++num_frees_from_stm_call;
                                ls->insertFree(arg);
                            } else {
                                assert(false);
                            }
                        //} else {
                          //  ++num_skipped_tm_calls;
                        }
                    }
                } else {
                    fFunctionCalls.insert(ci);
                    if (called) {
                        if (functionIsValid(called)) {
                            fFunctionCallSites.insert(std::pair<Function*,CallInst*>(called, ci));
                            funcQueue.push(called);
                        }
                    } else {
                        functionPointerBlocks.insert(ci);
                    }
                }
            }
        } else if (CastInst *ci = dyn_cast<CastInst>(I)) {
        } else if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(I)) {
        } else if (CmpInst *si = dyn_cast<CmpInst>(I)) {
        } else if (SelectInst *si = dyn_cast<SelectInst>(I)) {
        } else if (PHINode* phiNode = dyn_cast<PHINode>(I)) {
        } else if (isa<AllocaInst>(I)
            || isa<BinaryOperator>(I)) {
        } else if (AtomicRMWInst *ci = dyn_cast<AtomicRMWInst>(I)) {
            //TODO
        } else if (AtomicCmpXchgInst *ci = dyn_cast<AtomicCmpXchgInst>(I)) {
            //TODO
        } else if (isa<TerminatorInst>(I)) {
        } else if (isa<ExtractValueInst>(I)) {
        } else {
            DEBUG_WITH_TYPE("analyze", errs() << "Unhandled instruction: " << *I << "\n");
            //assert(false);
        }

        if (!ls->empty()) {
            DEBUG_WITH_TYPE("analyze", errs() << "Analyzed Intruction " << I << " with ");
            DEBUG_WITH_TYPE("analyze", ls->debugPrint());

            assert(fReservationSiteMap.find(I) == fReservationSiteMap.end());

            auto inserted = fReservationSiteMap.insert(std::pair<Instruction*,BlockDependancies*>(I,ls));
            assert(inserted.second);
            ++num_reservation_sites;
            memory_dependancies = true;
            ls = 0;
        }

        ++instr_i;
    }

    if (ls)
        delete ls;

    return memory_dependancies;
}

void ReserveTM::ReserveTMPass::getAnalyzedInstructions(Function * const function, InstructionSet& analyzedInstructions) {
    for (inst_iterator I = inst_begin(function), E = inst_end(function); I != E; ++I) {
        analyzedInstructions.insert(&*I);
    }
}


bool ReserveTM::ReserveTMPass::willReserveValue(CallInst* ci, ValueSet values, bool store, InstructionSet& visited ) {
    auto calledFunctions = getCalledFunctions(ci);
    for (auto called : calledFunctions) {
        //TODO: handle function pointers
        auto internal_arg = called->arg_begin();
        ValueSet new_values = values;
        for (unsigned arg_num = 0; arg_num < ci->getNumArgOperands(); ++arg_num, ++internal_arg) {
            Value *arg = ci->getArgOperand(arg_num);
            if (values.find(arg) != values.end()) {
                auto peers = AliasMapper::getPeers(internal_arg);
                new_values.insert(peers.begin(), peers.end());
            }
        }
        if (willReserveValue(&called->getEntryBlock(), new_values, store, visited)) {
            return true;
        }
    }

    return false;
}

bool ReserveTM::ReserveTMPass::willReserveValue(Instruction* instr, ValueSet values, bool store, InstructionSet& visited ) {
    if (visited.find(instr) != visited.end()) {
        return false;
    }
    visited.insert(instr);

    auto it = fReservationSiteMap.find(instr);
    if (it != fReservationSiteMap.end()) {
        auto ls = it->second;
        if (ls) {
            if (!store && ls->containsLoadFrom(values))
                return true;

            if (ls->containsStoreTo(values)) {
                return true;
            }
        }
    }

    if (CallInst *ci = dyn_cast<CallInst>(instr)) {
        return willReserveValue(ci, values, store, visited);
    }

    return false;
}

bool ReserveTM::ReserveTMPass::willReserveValue(BasicBlock* block, ValueSet values, bool store, InstructionSet& visited ) {
    for (BasicBlock::iterator i = block->begin(), e = block->end(); i != e; ++i) {
        if (visited.find(i) != visited.end()) {
            return false;
        }

        if (willReserveValue(i, values, store, visited))
            return true;
    }

    bool willReserve = false;
    for (succ_iterator si = succ_begin(block), si_e = succ_end(block); si != si_e; ++si) {
        BasicBlock *succ = *si;
        if (!willReserveValue(succ, values, store, visited))
            return false;

        willReserve = true;
    }

    return willReserve;
}

bool printIt = false;

ReserveTM::ReserveTMPass::CompressionResult ReserveTM::ReserveTMPass::canCompressValue(Instruction *instr, ValueSet values, bool store, InstructionSet& visited, bool skip, bool initial) {
    InstructionSet willReserveVisited = visited;
    auto inserted = visited.insert(instr);
    if (!inserted.second)
        return FAIL;

    // Out of transactional scope
    if (fAnalyzedInstructions.find(instr) == fAnalyzedInstructions.end()) {
        return FAIL;
    }

    if (printIt)
        DEBUG_WITH_TYPE("compress", errs() << "Compressing processing: " << *instr << "\n");
    //TODO: remove from value set;
    /*
       if (Instruction *i = dyn_cast<Instruction>(v)) {
       if (i->getParent() == block) {
       return FAIL;
       }
       }*/

    if (!initial) {
        auto entry = fReservationSiteMap.find(instr);
        if (entry != fReservationSiteMap.end()) {
            auto ls = (*entry).second;

            if (!store && ls->containsLoadFrom(values)) {
                return SUCCESS_INTRA_PROCEDURAL;
            }

            if (ls->containsStoreTo(values)) {
                return SUCCESS_INTRA_PROCEDURAL;
            }
        }
    }

    if (!skip) {
        if (CallInst* ci = dyn_cast<CallInst>(instr)) {
            InstructionSet willReserveVisited = visited;
            if (willReserveValue(ci, values, store, willReserveVisited)) {
                return SUCCESS_INTRA_PROCEDURAL;
            }
        }
    }

    CompressionResult canCompress = FAIL;
    auto preds = getPrevious(instr);
    for (auto pred : preds) {
        auto block = instr->getParent();
        auto func = block->getParent();

        ValueSet new_values = values;
        if (getFirstInstruction(func) == instr) {
            CallInst* ci = dyn_cast<CallInst>(pred);
            DEBUG_WITH_TYPE("compress", errs() << "Moving to callSite Instruction: " << ci << "\n");
            for (auto value : values) {
                if (Argument *arg = dyn_cast<Argument>(value)) {
                    if (arg->getParent() == func) {
                        auto fv = ci->getArgOperand(arg->getArgNo());
                        if (Constant *c = dyn_cast<Constant>(fv)) {
                            if (c->isNullValue()) {
                                canCompress = SUCCESS_INTER_PROCEDURAL;
                                continue;
                            }
                        }
                        auto peers = AliasMapper::getPeers(fv);
                        new_values.insert(peers.begin(), peers.end());
                    }
                }
            }
        }

        CompressionResult ret = canCompressValue(pred, new_values, store, visited, true);
        if (ret == FAIL) {
            return FAIL;
        } else {
            if (canCompress != SUCCESS_INTER_PROCEDURAL) {
                canCompress = ret;
            }
        }
    }

    return canCompress;
}

bool ReserveTM::ReserveTMPass::compressBlock(InstructionMap::const_iterator entry) {
    auto instr = (*entry).first;
    auto ls = (*entry).second;

    DEBUG_WITH_TYPE("compress", errs() << "Compressing Instruction: " << instr << "\n");

    //TODO: need to stop on defining instance
    //TODO: need to stop when at the highest transaction
    assert(ls && !ls->empty());

    size_t size = ls->size();
    compressBlockValues(entry, false);
    if (!ls->empty())
        compressBlockValues(entry, true);

    if (ls->empty()) {
        DEBUG_WITH_TYPE("compress", errs() << "Instruction: " << instr << " completely compressed\n");
        ++num_reservation_sites_completely_compressed;
        return true;
    }

    if (ls->size() != size) {
        DEBUG_WITH_TYPE("compress", errs() << "Instruction: " << instr << " partially compressed\n");
        ++num_reservation_sites_partially_compressed;
    }

    return false;
}

void ReserveTM::ReserveTMPass::compressBlockValues(InstructionMap::const_iterator entry, bool stores) {
    auto instr = (*entry).first;
    auto ls = (*entry).second;

    assert (ls && !ls->empty());

    ValueSet values;
    if (stores) {
        ls->copyStores(values);
    } else {
        ls->copyLoads(values);
    }

    ValueSet aliases;
    InstructionSet visited;
    for (auto value : values) {
        aliases.clear();
        visited.clear();

        CompressionResult canCompress = FAIL;
	bool thread_local = false;
	if (isFromAlloc(value)) {
	             thread_local = true;
		                 canCompress = SUCCESS_INTRA_PROCEDURAL;
				         
 }
 else
					 {
						             auto aliases = AliasMapper::getPeers(value);
							                 canCompress = canCompressValue(instr, aliases, stores, visited, true, true);
									         }

        if (canCompress != FAIL) {
            if (stores) {
                ++num_stores_compressed;
                if (canCompress == SUCCESS_INTER_PROCEDURAL)
                    ++num_stores_compressed_inter_procedurally;
        if (thread_local)
		                    ++num_stores_compressed_thread_local;
		ls->compressWithPreviousStore(value);
                //DEBUG_WITH_TYPE("compress", errs() << "Compressing Store: " << *value << " with aliases size: " << aliases.size() << "\n");
                /*if (aliases.size() > 1) {
                  DEBUG_WITH_TYPE("compress", errs() << "Aliases:\n");
                  DEBUG_WITH_TYPE("compress", printValues(aliases));
                  }*/
            } else {
                ++num_loads_compressed;
                if (canCompress == SUCCESS_INTER_PROCEDURAL)
                    ++num_loads_compressed_inter_procedurally;
		if (thread_local)
			                    ++num_loads_compressed_thread_local;
                ls->compressWithPreviousLoad(value);
                //DEBUG_WITH_TYPE("compress", errs() << "Compressing Load: " << *value << " with aliases size: " << aliases.size() << "\n");
                /*if (aliases.size() > 1) {
                  DEBUG_WITH_TYPE("compress", errs() << "Aliases:\n");
                  DEBUG_WITH_TYPE("compress", printValues(aliases));
                  }*/
                //}
        }
    }
}
}

bool ReserveTM::ReserveTMPass::eliminateLoads(InstructionMap::const_iterator entry, ValueSet& cachedEliminations, ValueSet& cachedNonEliminations) {
    auto instr = (*entry).first;
    auto ls = (*entry).second;

    DEBUG_WITH_TYPE("eliminate", errs() << "Elimination Processing for Instruction: " << instr << "\n");

    assert(ls);

    assert(!ls->empty());

    size_t size = ls->size();

    ValueSet values;
    ls->copyStores(values);
    for (auto storeValue : values) {
        if (isFromAlloc(storeValue)) {
            ++num_stores_eliminated_thread_local;
            ls->compressWithPreviousStore(storeValue);
        }
    }

    values.clear();
    ls->copyLoads(values);
    ValueSet aliases;
    for (auto loadValue : values) {
        if (isFromAlloc(loadValue)) {
            ++num_loads_eliminated_thread_local;
            ls->compressWithPreviousLoad(loadValue);
        }
#if 0
bool aliasesAreAlwaysFromAlloc = false;
        aliases.clear();
        if (cachedEliminations.find(loadValue) == cachedEliminations.end()) {
            if (cachedNonEliminations.find(loadValue) == cachedNonEliminations.end()) {
                if (!AliasMapper::getAliases(loadValue, aliases)) {
                    continue;
                }
bool fail = false;
                //TODO: is this right?
                for (auto value : aliases) {
                    if (!isFromAlloc(value) &&  !isa<Argument>(value)) {
fail = true;
break;                    
}
                }
if (!fail) {
            ++num_loads_eliminated_thread_local_whole;
            ls->compressWithPreviousLoad(loadValue);
aliasesAreAlwaysFromAlloc = true;
}
            }
        }

#endif
else if (strongIsolation)
	{
        bool canEliminate = true;
        aliases.clear();
        if (cachedEliminations.find(loadValue) == cachedEliminations.end()) {
            if (cachedNonEliminations.find(loadValue) != cachedNonEliminations.end()) {
                canEliminate = false;
            } else {
                if (!AliasMapper::getAliases(loadValue, aliases)) {
                    continue;
                }

                //TODO: is this right?
                for (auto it : fReservationSiteMap) {
                    auto bb_ls = it.second;
                    assert(bb_ls);

                    if (bb_ls->empty())
                        continue;

                    if (bb_ls->containsStoreTo(aliases)) {
                        canEliminate = false;
                        break;
                    }
                }
            }
        }

        if (canEliminate) {
            if (printAliasEliminate) {
                DEBUG_WITH_TYPE("eliminate", errs() << "At: " << instr << " want to get rid of: " << *loadValue << "\n");

                if (aliases.size() > 1) {
                    DEBUG_WITH_TYPE("eliminate", errs() << "Aliases:\n");
                    DEBUG_WITH_TYPE("eliminate", printValues(aliases));
                } else if (aliases.size() == 0) {
                    DEBUG_WITH_TYPE("eliminate", errs() << "Using cached result\n");
                }

            }
            ++num_loads_eliminated;

            ls->compressWithPreviousLoad(loadValue);

            cachedEliminations.insert(aliases.begin(), aliases.end());
        } else {
            cachedNonEliminations.insert(aliases.begin(), aliases.end());
        }
        }
    }

    if (ls->empty()) {
        DEBUG_WITH_TYPE("eliminate", errs() << "Instruction: " << instr << " completely eliminated\n");
        ++num_reservation_sites_completely_eliminated;
    } else if (ls->size() != size) {
        DEBUG_WITH_TYPE("eliminate", errs() << "Instruction: " << instr << " partially eliminated\n");
        ++num_reservation_sites_partially_eliminated;
    }

    return ls->empty();
}

void ReserveTM::ReserveTMPass::mergeValue(Instruction *instr, Value* value, bool store, std::queue<InstructionMap::const_iterator>& mergeQueue) {
    auto it = fReservationSiteMap.find(instr);
    if (it != fReservationSiteMap.end() && !it->second->empty()) {
        auto ls = it->second;
        if (store)
            ls->insertStore(value);
        else
            ls->insertLoad(value);
        //TODO: might be doing extra processing
        mergeQueue.push(it);
    } else {
        auto preds = getPrevious(instr);
        for (auto pred : preds) {
            auto block = instr->getParent();
            auto func = block->getParent();

            auto fv = value;
            if (getFirstInstruction(func) == instr) {
                CallInst* ci = dyn_cast<CallInst>(pred);
                DEBUG_WITH_TYPE("compress", errs() << "Moving to callSiteBlock: " << ci->getParent() << "\n");
                if (Argument *arg = dyn_cast<Argument>(value)) {
                    if (arg->getParent() == func) {
                        fv = ci->getArgOperand(arg->getArgNo());
                        if (Constant *c = dyn_cast<Constant>(fv)) {
                            if (c->isNullValue()) {
                                continue;
                            }
                        }
                    }
                }
            }

            mergeValue(pred, fv, store, mergeQueue);
        } 
    }
}

ReserveTM::ReserveTMPass::CompressionResult ReserveTM::ReserveTMPass::canMergeValue(Instruction* instr, Value* value, InstructionSet& visited, bool initial) {
    auto inserted = visited.insert(instr);
    if (!inserted.second)
        return FAIL;

    if (!initial) {
        //TODO: this is only valid if the funciton has absolutely no reservations
        if (CallInst* ci = dyn_cast<CallInst>(instr)) {
            auto it = fFunctionCalls.find(ci);
            if (it != fFunctionCalls.end())
                return FAIL;
        }

        if (instr == value) {
            return FAIL;
        }

        auto it = fReservationSiteMap.find(instr);
        if (it != fReservationSiteMap.end()) {
            auto ls = it->second;

            assert(ls);

            if (!ls->empty()) {
                return SUCCESS_INTRA_PROCEDURAL;
            }
        }
    }

    CompressionResult canMerge = FAIL;
    auto preds = getPrevious(instr);
    for (auto pred : preds) {
        auto block = instr->getParent();
        auto func = block->getParent();

        auto fv = value;
        if (getFirstInstruction(func) == instr) {
            CallInst* ci = dyn_cast<CallInst>(pred);
            DEBUG_WITH_TYPE("compress", errs() << "Moving to callSite Instruction: " << ci << "\n");
            if (Argument *arg = dyn_cast<Argument>(value)) {
                if (arg->getParent() == func) {
                    fv = ci->getArgOperand(arg->getArgNo());
                    if (Constant *c = dyn_cast<Constant>(fv)) {
                        if (c->isNullValue()) {
                            canMerge = SUCCESS_INTER_PROCEDURAL;
                            continue;
                        }
                    }
                }
            }
        }

        CompressionResult ret = canMergeValue(pred, fv, visited);
        if (ret == FAIL) {
            return FAIL;
        } else {
            if (canMerge != SUCCESS_INTER_PROCEDURAL) {
                canMerge = ret;
            }
        }
    }

    return canMerge;
}

Instruction * blah = 0;

bool ReserveTM::ReserveTMPass::mergeBlock(InstructionMap::const_iterator entry, std::queue<InstructionMap::const_iterator>& mergeQueue) {
    auto instr = (*entry).first;
    auto ls = (*entry).second;

    DEBUG_WITH_TYPE("merge", errs() << "Merge Processing for Instr: " << instr << "\n");
    //TODO: need to stop on defining instance
    //TODO: need to stop when at the highest transaction

    if (instr == blah)
        assert(ls && !ls->empty());

    size_t size = ls->size();
    auto num_entries = ls->numOrderedLoadsStores();
    Value * args[num_entries];
    uint32_t bit_vector = ls->copyLoadsStores(args);
    InstructionSet visited;

    for (auto it = args; it != args+num_entries; ++it) {
        Value *value = *it;
        bool store = bit_vector & 1;
        bit_vector = bit_vector >> 1;

        visited.clear();
        CompressionResult canMerge = canMergeValue(instr, value, visited, true);

        if (canMerge == FAIL)
            break;

        if (store) {
            ++num_stores_merged;
            if (canMerge == SUCCESS_INTER_PROCEDURAL)
                ++num_stores_merged_inter_procedurally;
            ls->compressWithPreviousStore(value);
        } else {
            ++num_loads_merged;
            if (canMerge == SUCCESS_INTER_PROCEDURAL)
                ++num_loads_merged_inter_procedurally;
            ls->compressWithPreviousLoad(value);
        }

        auto preds = getPrevious(instr);
        for (auto pred : preds) {
            mergeValue(pred, value, store, mergeQueue);
        }
    }

    if (ls->empty()) {
        DEBUG_WITH_TYPE("merge", errs() << "Instruction: " << instr << " completely merged\n");
        ++num_reservation_sites_completely_merged;
        return true;
    }

    if (ls->size() != size)
        ++num_reservation_sites_partially_merged;

    return false;
}

bool ReserveTM::ReserveTMPass::calcReadsWrites(CallInst* ci, uint32_t* instrs, uint32_t* reads, uint32_t* writes, InstructionSet& visited ) {
    auto calledFunctions = getCalledFunctions(ci);
    uint32_t new_instrs = 0;
    uint32_t new_reads = 0;
    uint32_t new_writes = 0;

    for (auto called : calledFunctions) {
        //TODO: handle function pointers
    uint32_t cur_instrs = 0;
	uint32_t cur_reads = 0;
	uint32_t cur_writes = 0;

        if (!calcReadsWrites(&called->getEntryBlock(), &cur_instrs, &cur_reads, &cur_writes, visited)) {
            return false;
        }

	if (cur_instrs > new_instrs)
		new_instrs = cur_instrs;

	if (cur_reads > new_reads)
		new_reads = cur_reads;

	if (cur_writes > new_writes)
		new_writes = cur_writes;
    }

    *instrs += new_instrs;
    *reads += new_reads;
    *writes += new_writes;

    return true;
}

bool ReserveTM::ReserveTMPass::calcReadsWrites(Instruction* instr, uint32_t* instrs, uint32_t* reads, uint32_t* writes, InstructionSet& visited ) {
    if (fAnalyzedInstructions.find(instr) == fAnalyzedInstructions.end()) {
    return true;
    }

	    if (visited.find(instr) != visited.end()) {
        return false;
    }
    visited.insert(instr);

    auto it = fReservationSiteMap.find(instr);
    if (it != fReservationSiteMap.end()) {
        auto ls = it->second;
        if (ls && !ls->empty()) {
	    ++instrs;
	    reads += ls->numReads();
	    writes += ls->numWrites();
        }
    }

    if (CallInst *ci = dyn_cast<CallInst>(instr)) {
        return calcReadsWrites(ci, instrs, reads, writes, visited);
    }

    return true;
}

bool ReserveTM::ReserveTMPass::calcReadsWrites(BasicBlock* block, uint32_t* instrs, uint32_t* reads, uint32_t* writes, InstructionSet& visited, Instruction* start) {

    for (BasicBlock::iterator i = block->begin(), e = block->end(); i != e; ++i) {
	    Instruction *I = i;
    if (fAnalyzedInstructions.find(I) == fAnalyzedInstructions.end()) {
    return true;
    }
	    if (start) {
	    if (I == start) {
		    start == NULL;
	    }
	    } else {
        if (visited.find(i) != visited.end()) {
            return false;
        }

        if (!calcReadsWrites(i, instrs, reads, writes, visited))
            return false;
	    }
    }

    uint32_t new_instrs = 0;
    uint32_t new_reads = 0;
    uint32_t new_writes = 0;

    if (succ_begin(block) != succ_end(block))
    {
	    for (succ_iterator si = succ_begin(block), si_e = succ_end(block); si != si_e; ++si) {
        BasicBlock *succ = *si;
    uint32_t cur_instrs = 0;
	uint32_t cur_reads = 0;
	uint32_t cur_writes = 0;

        if (!calcReadsWrites(succ, &cur_instrs, &cur_reads, &cur_writes, visited)) {
            return false;
        }

	if (cur_instrs > new_instrs)
		new_instrs = cur_instrs;

	if (cur_reads > new_reads)
		new_reads = cur_reads;

	if (cur_writes > new_writes)
		new_writes = cur_writes;
    }
}
    else
    {
    auto preds = getPrevious(block->getParent());
    for (auto pred : preds) {

    uint32_t cur_instrs = 0;
	uint32_t cur_reads = 0;
	uint32_t cur_writes = 0;

        if (!calcReadsWrites(pred->getParent(), &cur_instrs, &cur_reads, &cur_writes, visited, pred)) {
            return false;
        }

	if (cur_instrs > new_instrs)
		new_instrs = cur_instrs;

	if (cur_reads > new_reads)
		new_reads = cur_reads;

	if (cur_writes > new_writes)
		new_writes = cur_writes;
    }
    }

    *instrs += new_instrs;
    *reads += new_reads;
    *writes += new_writes;

    return true;
}

bool ReserveTM::ReserveTMPass::runOnModule(Module &M) {
    llvm::Statistic *num_stm_reserve[4];
    std::queue<Function *> funcQueue;
    FunctionSet fAdded;

    stm_reserve[0] = dyn_cast<Function>(M.getOrInsertFunction("stmreserve01",
            Type::getVoidTy(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            Type::getInt64Ty(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            NULL));
    num_stm_reserve[0] = &num_stm_reserve_1;
    stm_reserve[1] = dyn_cast<Function>(M.getOrInsertFunction("stmreserve02",
            Type::getVoidTy(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            Type::getInt64Ty(M.getContext()),
            Type::getInt64Ty(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            NULL));
    num_stm_reserve[1] = &num_stm_reserve_2;
    stm_reserve[2] = dyn_cast<Function>(M.getOrInsertFunction("stmreserve03",
            Type::getVoidTy(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            Type::getInt64Ty(M.getContext()),
            Type::getInt64Ty(M.getContext()),
            Type::getInt64Ty(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            NULL));
    num_stm_reserve[2] = &num_stm_reserve_3;
    stm_reserve[3] = dyn_cast<Function>(M.getOrInsertFunction("stmreserve04",
            Type::getVoidTy(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            Type::getInt64Ty(M.getContext()),
            Type::getInt64Ty(M.getContext()),
            Type::getInt64Ty(M.getContext()),
            Type::getInt64Ty(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            Type::getInt32Ty(M.getContext()),
            NULL));
    num_stm_reserve[3] = &num_stm_reserve_4;

    for (auto i = M.begin(), ie = M.end(); i != ie; ++i) {
        auto func = i;
        // Automatically add *txfunc*() functions to system
        // TODO: Use clang to insert LLVM instructions to start/end a transaction
        if (func->getName().str().find("txfunc") != std::string::npos) {
            DEBUG_WITH_TYPE("analyze", errs() << "Found transaction start function: ");
            DEBUG_WITH_TYPE("analyze", errs().write_escaped(func->getName()));
            DEBUG_WITH_TYPE("analyze", errs() << "\n");
            funcQueue.push(func);
            fTxFunctions.insert(func);
        }
    }

    if (fTxFunctions.empty())
        return false;

    // Process each function
    while (!funcQueue.empty()) {
        auto func = funcQueue.front();
        funcQueue.pop();

        auto it = fAdded.find(func);
        if (it == fAdded.end()) {
            fAdded.insert(func);

            DEBUG_WITH_TYPE("analyze", errs() << "============================================================================\n");
            DEBUG_WITH_TYPE("analyze", errs() << "Analyzing Function: ");
            DEBUG_WITH_TYPE("analyze", (func->hasName() ? (errs().write_escaped(func->getName()) << "\n") : (errs() << "*NONE*\n")));
            DEBUG_WITH_TYPE("analyze", errs() << "============================================================================\n");

            assert(func->size());

            if (analyzeFunction(func, fAnalyzedInstructions, funcQueue, fFunctionPointerBlocks)) {
                ++num_functions_with_memory_dependancies;
            }
        }
    }
/*
    InstructionSet FunctionPointerAnalyzedBlocks = fAnalyzedInstructions;
    InstructionSet FunctionPointerBlocks;
    FunctionSet fAdded2 = fAdded;
    for (auto i = M.begin(), ie = M.end(); i != ie; ++i) {
        auto func = i;
        if (func->hasAddressTaken() && func->size()
            && (func->getName().str().find("_ZN3stm") == std::string::npos)
            && (func->getName().str().find("cbr_nn") == std::string::npos)
            && (func->getName().str().find("begin") == std::string::npos)
            && (func->getName().str().find("client_run") == std::string::npos)
            && (func->getName().str().find("6commit") == std::string::npos)
            && (func->getName().str().find("4read") == std::string::npos)
            && (func->getName().str().find("5write") == std::string::npos)
            && (func->getName().str().find("commit_ro") == std::string::npos)
            && (func->getName().str().find("read_ro") == std::string::npos)
            && (func->getName().str().find("write_ro") == std::string::npos)
            && (func->getName().str().find("commit_rw") == std::string::npos)
            && (func->getName().str().find("read_rw") == std::string::npos)
            && (func->getName().str().find("write_rw") == std::string::npos)
            && (func->getName().str().find("rollback") == std::string::npos)
            && (func->getName().str().find("irrevoc") == std::string::npos)
            && (func->getName().str().find("onSwitchTo") == std::string::npos)
           ) {
            auto it = fAdded2.find(func);
            if (it == fAdded2.end()) {

                DEBUG_WITH_TYPE("analyze", errs() << "============================================================================\n");
                DEBUG_WITH_TYPE("analyze", errs() << "Analyzing Function Pointer: ");
                DEBUG_WITH_TYPE("analyze", (func->hasName() ? (errs().write_escaped(func->getName()) << "\n") : (errs() << "*NONE*\n")));
                DEBUG_WITH_TYPE("analyze", errs() << "============================================================================\n");
                fAdded2.insert(func);

                if (analyzeFunction(func, FunctionPointerAnalyzedBlocks, funcQueue, FunctionPointerBlocks)) {
                    ++num_functions_with_memory_dependancies;
                }
            }
        }
    }
    */
    /*
       while (!funcQueue.empty()) {
       auto func = funcQueue.front();
       funcQueue.pop();

       DEBUG_WITH_TYPE("analyze", errs() << "============================================================================\n");
       DEBUG_WITH_TYPE("analyze", errs() << "Analyzing Function (from function pointer): ");
       DEBUG_WITH_TYPE("analyze", (func->hasName() ? (errs().write_escaped(func->getName()) << "\n") : (errs() << "*NONE*\n")));
       DEBUG_WITH_TYPE("analyze", errs() << "============================================================================\n");

       assert(func->size());

       if (analyzeFunction(&func, FunctionPointerAnalyzedBlocks, funcQueue)) {
       ++num_functions_with_memory_dependancies;
       }
       }
       */
    AliasMapper::analyzeModule(M);

    ValueSet aliases;
    for (auto instr : fFunctionPointerBlocks) {
        aliases.clear();

        CallInst* ci = dyn_cast<CallInst>(instr);

        assert(AliasMapper::getAliases(ci->getCalledValue(), aliases) && (aliases.size() > 1));

        /*DEBUG_WITH_TYPE("func", errs() << "Function Pointer at: " << block << " (" << *ci->getCalledValue() << ") has " << aliases.size() << " aliases\n");
          if (aliases.size() > 1) {
          DEBUG_WITH_TYPE("func", errs() << "Aliases:\n");
          DEBUG_WITH_TYPE("func", printValues(aliases));
          }*/
        for (auto alias : aliases) {
            if (Function* func = dyn_cast<Function>(alias)) {
                fFunctionCallSites.insert(std::pair<Function*,CallInst*>(func, ci));
                auto it = fAdded.find(func);
                if (it == fAdded.end()) {
                    assert(func->hasName());
                    
                    DEBUG_WITH_TYPE("analyze", errs() << "============================================================================\n");
                    DEBUG_WITH_TYPE("analyze", errs() << "Analyzing Function (from function pointer): ");
                    DEBUG_WITH_TYPE("analyze", (func->hasName() ? (errs().write_escaped(func->getName()) << "\n") : (errs() << "*NONE*\n")));
                    DEBUG_WITH_TYPE("analyze", errs() << "============================================================================\n");

                    getAnalyzedInstructions(func, fAnalyzedInstructions);
                    if (analyzeFunction(func, fAnalyzedInstructions, funcQueue, fFunctionPointerBlocks)) {
                        ++num_functions_with_memory_dependancies;
                    }
                }
            }
        }
    }

    while (!funcQueue.empty()) {
        auto func = funcQueue.front();
        funcQueue.pop();

        auto it = fAdded.find(func);
        if (it == fAdded.end()) {
            fAdded.insert(func);

            DEBUG_WITH_TYPE("analyze", errs() << "============================================================================\n");
            DEBUG_WITH_TYPE("analyze", errs() << "Analyzing Function (Pointer pass): ");
            DEBUG_WITH_TYPE("analyze", (func->hasName() ? (errs().write_escaped(func->getName()) << "\n") : (errs() << "*NONE*\n")));
            DEBUG_WITH_TYPE("analyze", errs() << "============================================================================\n");

            assert(func->size());

            if (analyzeFunction(func, fAnalyzedInstructions, funcQueue, fFunctionPointerBlocks)) {
                ++num_functions_with_memory_dependancies;
            }
        }
    }

    //TODO: function blocks of called functions
    //TODO: need aliasing on function pointers args

    num_instructions_analyzed = fAnalyzedInstructions.size();
    num_functions_with_memory_dependancies = fAdded.size();

    for (auto entry = fReservationSiteMap.begin(); entry != fReservationSiteMap.end(); ++entry) {
        auto instr = (*entry).first;
        if (fAnalyzedInstructions.find(instr) == fAnalyzedInstructions.end()) {
            DEBUG_WITH_TYPE("analyze", errs() << "Pruning Instr: " << instr << "\n");
            fReservationSiteMap.erase(entry);
            entry = fReservationSiteMap.begin();
        }
    }

    // Eliminate Pass
    std::queue<InstructionMap::const_iterator> compressionQueue;
    ValueSet cachedEliminations;
    ValueSet cachedNonEliminations;
    for (auto entry = fReservationSiteMap.begin(); entry != fReservationSiteMap.end(); ++entry) {
        auto ls = (*entry).second;
        assert(ls);

        if (ls->empty())
            continue;

        if (!eliminate || !eliminateLoads(entry, cachedEliminations, cachedNonEliminations))
            compressionQueue.push(entry);
    }

    // Compression Pass
    std::queue<InstructionMap::const_iterator> mergeQueue;
    while (!compressionQueue.empty()) {
        auto entry = compressionQueue.front();
        compressionQueue.pop();
        if (!compressBlock(entry))
            mergeQueue.push(entry);
    }
    
    // Merge Pass
    while (!mergeQueue.empty()) {
        auto entry = mergeQueue.front();
        mergeQueue.pop();

	//if (singleWriter && hasPreviousStore(entry))
	//	++num_reservation_sites_with_previous_store;

        if (merge)
            mergeBlock(entry, mergeQueue);
    }

    //Analyze Pass
    InstructionSet visited;
int index = 0;
    for (auto entry : fReservationSiteMap) {
        auto ls = entry.second;

        assert(ls);

        if (ls->empty())
            continue;

            auto instr = entry.first;
	uint32_t reads = 0;
uint32_t writes = 0;
uint32_t instrs = 0;

            visited.clear();
/*
if (calcReadsWrites(instr->getParent(), &instrs, &reads, &writes, visited, instr)) {
			ls->setUpcomingInstructions(instrs);
			ls->setUpcomingReads(reads);
			ls->setUpcomingWrites(writes);
			if (instrs == 0)
				++num_reservation_sites_at_end;
		} else
*/
{
			ls->setUpcomingInstructions(1000+index);
			ls->setUpcomingReads(10000+index);
			ls->setUpcomingWrites(10000+index);
++index;
//++num_reservation_sites_followed_by_loop;
		}
    }

    num_functions = fAdded.size();
    num_functions_pointer_calls = fFunctionPointerBlocks.size();

    for (Function* func : fAdded) {
        if (func->size()) {
            for (inst_iterator I = inst_begin(func), E = inst_end(func); I != E; ++I) {
                auto found_it = fReservationSiteMap.find(&*I);
                if (found_it != fReservationSiteMap.end()) {
                    auto ls = (*found_it).second;

                    assert(ls);

                    if (!ls->empty()) {
                        ++num_functions_instrumented;
                        break;
                    }
                }
            }
        }
    }

    // Instrument Pass
    for (auto entry : fReservationSiteMap) {
        auto ls = entry.second;

        assert(ls);

        if (ls->empty())
            continue;

        auto instr = entry.first;
        auto num_entries = ls->numOrderedLoadsStores();
        if (num_entries > 0) {
            DEBUG_WITH_TYPE("instrument", errs() << "Instrumenting Instruction: " << instr << " ");
            DEBUG_WITH_TYPE("instrument", ls->debugPrint());

            Value * args[num_entries + 4];
            uint32_t bit_vector = ls->copyLoadsStores(args + 1);

            for (auto i = 1; i <= num_entries; ++i) {
                args[i] = CastInst::CreatePointerCast (args[i], Type::getInt64Ty(args[i]->getContext()), "", instr);
            }
            args[0] = ConstantInt::get(IntegerType::get(M.getContext(), 32), bit_vector, true);
	    unsigned cur_entry = num_entries + 1;
            args[cur_entry++] = ConstantInt::get(IntegerType::get(M.getContext(), 32), ls->upcomingInstructions(), true);
            args[cur_entry++] = ConstantInt::get(IntegerType::get(M.getContext(), 32), ls->upcomingReads(), true);
            args[cur_entry++] = ConstantInt::get(IntegerType::get(M.getContext(), 32), ls->upcomingWrites(), true);
            CallInst::Create(stm_reserve[num_entries - 1], ArrayRef<Value*>(args, num_entries + 4), "", instr);

            ++(*num_stm_reserve[num_entries - 1]);
            ++num_reservation_sites_instrumented;
        } else {
            ++num_reservation_sites_skipped;
        }
    }

    return true;
}
