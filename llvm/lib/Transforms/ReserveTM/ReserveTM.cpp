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

#define MAX_RESERVATIONS 7

STATISTIC(num_stm_reserve_1,                            "4.1    STM reservations with 1 entry");
STATISTIC(num_stm_reserve_2,                            "4.2    STM reservations with 2 entries");
STATISTIC(num_stm_reserve_3,                            "4.3    STM reservations with 3 entries");
STATISTIC(num_stm_reserve_4,                            "4.4    STM reservations with 4 entries");
STATISTIC(num_stm_reserve_5,                            "4.5    STM reservations with 5 entries");
STATISTIC(num_stm_reserve_6,                            "4.6    STM reservations with 6 entries");
STATISTIC(num_stm_reserve_7,                            "4.7    STM reservations with 7 entries");

STATISTIC(num_loads_compressed,                         "5.1.1  Loads compressed");
STATISTIC(num_loads_compressed_inter_procedurally,      "5.1.2  Loads compressed inter-procedurally");
STATISTIC(num_loads_compressed_thread_local,            "5.1.3  Loads compressed thread local");
STATISTIC(num_loads_eliminated_thread_local,            "5.1.3  Loads eliminated thread local");
STATISTIC(num_loads_eliminated_thread_local_whole,      "5.1.4  Loads eliminated thread local (whole)");
STATISTIC(num_loads_merged,                             "5.2.1  Loads merged");
STATISTIC(num_loads_merged_inter_procedurally,          "5.2.2  Loads merged inter-procedurally");

STATISTIC(num_stores_compressed,                        "6.1.1  Stores compressed");
STATISTIC(num_stores_compressed_inter_procedurally,     "6.1.2  Stores compressed inter-procedurally");
STATISTIC(num_stores_compressed_thread_local,           "6.1.3  Stores compressed thread local");
STATISTIC(num_stores_eliminated_thread_local,           "6.1.3  Stores eliminated thread local");
STATISTIC(num_stores_merged,                            "6.2.1  Stores merged");
STATISTIC(num_stores_merged_inter_procedurally,         "6.2.2  Stores merged inter-procedurally");

STATISTIC(num_eliminated_loads,                         "7.1    Eliminated loads");
STATISTIC(num_eliminated_stores,                        "7.2    Eliminated stores");

STATISTIC(num_compression_attempted,                    "8.1    Compressions attempted");
STATISTIC(num_compression_succeeded,                    "8.2    Compressions succeeded");
STATISTIC(num_compression_succeeded_simple,             "8.3    Compressions succeeded (simple)");
STATISTIC(num_compression_aborts_from_exit,             "8.3.1  Compression aborts from exit");
STATISTIC(num_compression_aborts_from_recursion,        "8.3.2  Compression aborts from recursion");
STATISTIC(num_compression_aborts_from_partial_paths,    "8.3.3  Compression aborts from partial paths");

STATISTIC(num_merge_definition_moves,                   "9.2.5  Merge definition moves");
STATISTIC(num_merge_aborts_from_function_calls,         "9.3.3  Merge aborts from function calls");
STATISTIC(num_merge_aborts_from_partial_paths,          "9.3.4  Merge aborts from partial paths");
STATISTIC(num_merge_aborts_from_definition,             "9.3.5  Merge aborts from definition");

bool printAliasEliminate = false;
bool compress = true;
bool eliminate = false;
bool strongIsolation = false;
bool merge = false;
bool singleWriter = true;
bool fullInstrumentation = false;
bool replaceInstrumentation = true;
Type* txType;

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

    typedef std::map<Instruction *, ReservationSite*> InstructionMap;
    InstructionMap fReservationSiteMap;

    typedef std::set<ReservationSite*> ReservationSiteSet;

    enum CompressionResult
    {
      FAIL,
      SUCCESS_INTER_PROCEDURAL,
      SUCCESS_INTRA_PROCEDURAL,
    };

    bool eliminateLoads(InstructionMap::const_iterator entry, ValueSet& cachedEliminations, ValueSet& cachedNonEliminations);
    ReservationSiteSet willReserveValue(BasicBlock* block, ValueSet values, bool store, InstructionSet& visited );
    ReservationSiteSet willReserveValue(Instruction* instr, ValueSet values, bool store, InstructionSet& visited );
    ReservationSiteSet willReserveValue(CallInst* ci, ValueSet values, bool store, InstructionSet& visited );
    ReservationSiteSet compressStoreIntoLoad(Instruction *instr, ValueSet values, InstructionSet& visited, bool skip = false, bool initial = false);
    ReservationSiteSet CompressionSitesValue(Instruction *instr, ValueSet values, bool store, InstructionSet& visited, bool skip = false, bool initial = false);
    bool compressSite(InstructionMap::const_iterator entry);
    ReservationSiteSet canMergeValue(Instruction *instr, Value* v, InstructionSet& visited, bool initial = false);
    bool mergeBlock(InstructionMap::const_iterator entry, std::queue<InstructionMap::const_iterator>& mergeQueue);

    bool calcReadsWrites(CallInst* ci, uint32_t* instrs, uint32_t* reads, uint32_t* writes, InstructionSet& visited);
    bool calcReadsWrites(Instruction* instr, uint32_t* instrs, uint32_t* reads, uint32_t* writes, InstructionSet& visited);
    bool calcReadsWrites(BasicBlock* block, uint32_t* instrs, uint32_t* reads, uint32_t* writes, InstructionSet& visited, Instruction* start = NULL);

    std::multimap<Function *, CallInst *> fFunctionCallSites;
    std::set<CallInst*> fFunctionCalls;
    InstructionSet fFunctionPointerBlocks;
    BasicBlockSet fCompressedBlocks;
    std::queue<Function *> fFunctionPointerQueue;


    InstructionSet isFromAlloc(Value *v) {
      InstructionSet RetVal;
      if (Instruction *I = dyn_cast<Instruction>(v)) {
        if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(I)) {
          return isFromAlloc(gep->getPointerOperand());
#if 0
        } else if (PtrToIntInst *pt = dyn_cast<PtrToIntInst>(I)) {
          //TODO: be more rigorous
          return isFromAlloc(pt->getOperand(0));
#endif
        } else if (BitCastInst *bc = dyn_cast<BitCastInst>(I)) {
          //TODO: be more rigorous
          return isFromAlloc(bc->getOperand(0));
        } else if (CallInst *ci = dyn_cast<CallInst>(I)) {
#if 1
          auto func = ci->getCalledFunction();
          if (func && func->hasName() && ((func->getName().str().find("malloc") != std::string::npos) || (func->getName().str().find("tx_alloc") != std::string::npos))) {
            RetVal.insert(I);
          }
#endif
        } else if (isa<AllocaInst>(I)) {
          RetVal.insert(I);
        }
      } else if (Argument *arg = dyn_cast<Argument>(v)) {
        Function *func = arg->getParent();
        auto ret = fFunctionCallSites.equal_range(func);
        for (auto callSiteIt=ret.first; callSiteIt!=ret.second; ++callSiteIt) {
          auto ci = (*callSiteIt).second;
          auto CallSiteVals = isFromAlloc(ci->getArgOperand(arg->getArgNo()));

          // If one of the call sites failed, then return an empty set
          if (CallSiteVals.empty())
            return CallSiteVals;

          RetVal.insert(CallSiteVals.begin(), CallSiteVals.end());
        }

        return RetVal;
      }

      return RetVal;
    }


    Instruction * getFirstInstruction(Function * func) {
      return &*func->getEntryBlock().begin();
    }

    std::set<Instruction*> getPrevious(Instruction* I, bool singleBlock = false) {
      std::set<Instruction*> prev;
      auto block = I->getParent();
      if (I == block->begin()) {
        //TODO: this is a hack
        if (singleBlock)
          return prev;

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

    Instruction* moveUp(Instruction* I) {
      //std::set<Instruction*> prev;
      auto block = I->getParent();
      if (I == block->begin()) {
        //TODO: Handle correctly
        return 0;
#if 0
        //TODO: this is a hack
        if (singleBlock)
          return prev;

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
#endif
      } else {
        for (auto instr_i = block->begin(), instr_e = block->end(); instr_i != instr_e; ++instr_i) {
          if (&*instr_i == I) {
            //prev.insert(--instr_i);
            --instr_i;
            if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(I)) {
              if (isa<LoadInst>(instr_i) && (instr_i != gep->getPointerOperand())) {
                I->moveBefore(instr_i);
                return instr_i;
              } else if (isa<StoreInst>(instr_i)) {
                I->moveBefore(instr_i);
                return instr_i;
              }
            }
            break;
          }
        }
      }

      return 0;//prev;
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

    Function* stm_reserve[MAX_RESERVATIONS];
    FunctionSet fTxFunctions;
  };
}

char ReserveTM::ReserveTMPass::ID = 0;
#if 1
static RegisterPass<ReserveTM::ReserveTMPass> X("ReserveTM", "ReserveTM World Pass");
#else
static const char ReserveTM::ReserveTMPass_name[] = "ReserveTM::ReserveTMPass World Pass";
INITIALIZE_PASS_BEGIN(ReserveTM::ReserveTMPass, "ReserveTM::ReserveTMPass", ReserveTM::ReserveTMPass_name, false, false);
INITIALIZE_AG_DEPENDENCY(AliasAnalysis);
INITIALIZE_PASS_END(ReserveTM::ReserveTMPass, "ReserveTM::ReserveTMPass", ReserveTM::ReserveTMPass_name, false, false);
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
      && (func->getName().str().find("stmreserve") == std::string::npos)
      && (func->getName().str().find("pthread") == std::string::npos)) {
      return true;
    }

    return false;
  }

}

using namespace ReserveTM;

ReserveTM::ReserveTMPass::ReserveTMPass() : ModulePass(ID) {
  for (int i = 0; i < MAX_RESERVATIONS; ++i) {
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
  bool replacement_instruction = false;
  Value *txValue;
  ReservationSite* Site = 0;
  for (inst_iterator instr_i = inst_begin(function), E = inst_end(function); instr_i != E; ) {
    Instruction *I = &*instr_i;
    DEBUG_WITH_TYPE("analyze", errs() << "Instr: (" << I << ") ");
    DEBUG_WITH_TYPE("analyze", printInst(I, true));
    DEBUG_WITH_TYPE("analyze", errs() << "\n");

    if (!replacement_instruction &&(analyzedInstructions.find(I) != analyzedInstructions.end()))
      return false;

    analyzedInstructions.insert(I);

    if (LoadInst *li = dyn_cast<LoadInst>(I)) {
      ++num_loads;
      if (replacement_instruction || fullInstrumentation) {
        Site = new ReservationSite(I, li->getPointerOperand(), ReservationSite::LOAD, !replacement_instruction);
        replacement_instruction = false;
        Site->tx = txValue;
        if (txType != Site->tx->getType())
          txType = Site->tx->getType();
      }
    } else if (StoreInst *si = dyn_cast<StoreInst>(I)) {
      ++num_stores;
      if (replacement_instruction || fullInstrumentation) {
        Site = new ReservationSite(I, si->getPointerOperand(), ReservationSite::STORE, !replacement_instruction);
        replacement_instruction = false;
        Site->tx = txValue;
        if (txType != Site->tx->getType())
          txType = Site->tx->getType();
      }
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
            Site = new ReservationSite(I, ci, ReservationSite::ALLOC);
            //Site->tx =function->arg_begin();
            //if (txType != Site->tx->getType())
            //txType = Site->tx->getType();
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
                AttrListPtr attr = called->getAttributes();
                //    DEBUG_WITH_TYPE("analyze", errs() << "Function Attributes: " << called->getAttributes().getFnAttributes().getAsString() << "\n");
#if 1
                if (replaceInstrumentation) {
                  Instruction *newI = new LoadInst(arg, "newRead", false);
                  ReplaceInstWithInst(ci, newI);
                  instr_i = inst_begin(function);
                  while (&*instr_i != newI) {
                    ++instr_i;
                  }
                  txValue = ci->getArgOperand(1);
                  replacement_instruction = true;
                  continue;
#if 0
                } else {
                  ++num_loads;
                  Site->insertLoad(arg);
                  Site->tx = ci->getArgOperand(1);
                  if (txType != Site->tx->getType())
                    txType = Site->tx->getType();
#endif
                }
#endif
              } else if (called->getName().str().find("stm_write") != std::string::npos) {
                ++num_stores_from_stm_call;
                AttrListPtr attr = called->getAttributes();
                //    DEBUG_WITH_TYPE("analyze", errs() << "Function Attributes: " << called->getAttributes().getFnAttributes().getAsString() << "\n");
#if 1
                if (replaceInstrumentation) {
                  Instruction *newI = new StoreInst(ci->getArgOperand(1), arg, false);
                  ReplaceInstWithInst(ci, newI);
                  instr_i = inst_begin(function);
                  while (&*instr_i != newI) {
                    ++instr_i;
                  }
                  txValue = ci->getArgOperand(2);
                  replacement_instruction = true;
                  continue;
#if 0
                } else {
                  ++num_stores;
                  Site->insertStore(arg);
                  Site->tx = ci->getArgOperand(2);
                  if (txType != Site->tx->getType())
                    txType = Site->tx->getType();
#endif
                }
#endif
              } else if (called->getName().str().find("tx_free") != std::string::npos) {
                ++num_frees;
                ++num_frees_from_stm_call;
                Site = new ReservationSite(I, arg, ReservationSite::FREE);
                //  Site->tx =function->arg_begin();
                //if (txType != Site->tx->getType())
                //  txType = Site->tx->getType();
              } else {
                assert(false);
                //++num_skipped_tm_calls;
              }
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

    if (Site) {
      DEBUG_WITH_TYPE("analyze", errs() << "Analyzed Intruction " << I << " with ");
      DEBUG_WITH_TYPE("analyze", Site->debugPrint());

      assert(fReservationSiteMap.find(I) == fReservationSiteMap.end());

      auto inserted = fReservationSiteMap.insert(std::pair<Instruction*,ReservationSite*>(I, Site));
      assert(inserted.second);
      ++num_reservation_sites;
      memory_dependancies = true;
      Site = 0;
    }

    ++instr_i;
  }

  //if (Site)
  //  delete ls;

  return memory_dependancies;
}

void ReserveTM::ReserveTMPass::getAnalyzedInstructions(Function * const function, InstructionSet& analyzedInstructions) {
  for (inst_iterator I = inst_begin(function), E = inst_end(function); I != E; ++I) {
    analyzedInstructions.insert(&*I);
  }
}


std::set<ReservationSite*> ReserveTM::ReserveTMPass::willReserveValue(CallInst* ci, ValueSet values, bool store, InstructionSet& visited ) {
  ReservationSiteSet RetVal;
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
    RetVal = willReserveValue(&called->getEntryBlock(), new_values, store, visited);
    if (!RetVal.empty()) {
      return RetVal;
    }
  }

  return RetVal;
}

std::set<ReservationSite*> ReserveTM::ReserveTMPass::willReserveValue(Instruction* instr, ValueSet values, bool store, InstructionSet& visited ) {
  ReservationSiteSet RetVal;
  if (visited.find(instr) != visited.end()) {
    return RetVal;
  }

  visited.insert(instr);

  auto it = fReservationSiteMap.find(instr);
  if (it != fReservationSiteMap.end()) {
    auto Site = it->second;
    if (Site) {
      if (!store && Site->containsLoadFrom(values))
        RetVal.insert(Site);
      return RetVal;

      if (Site->containsStoreTo(values)) {
        RetVal.insert(Site);
        return RetVal;
      }
    }
  }

  if (CallInst *ci = dyn_cast<CallInst>(instr)) {
    RetVal = willReserveValue(ci, values, store, visited);
  }

  return RetVal;
}

std::set<ReservationSite*> ReserveTM::ReserveTMPass::willReserveValue(BasicBlock* block, ValueSet values, bool store, InstructionSet& visited ) {
  ReservationSiteSet RetVal;
  for (BasicBlock::iterator i = block->begin(), e = block->end(); i != e; ++i) {
    if (visited.find(i) != visited.end()) {
      return RetVal;
    }

    RetVal = willReserveValue(i, values, store, visited);
    if (!RetVal.empty())
      return RetVal;
  }

  for (succ_iterator si = succ_begin(block), si_e = succ_end(block); si != si_e; ++si) {
    BasicBlock *succ = *si;
    auto NewRetVal = willReserveValue(succ, values, store, visited);
    if (NewRetVal.empty())
      return NewRetVal;

    RetVal.insert(NewRetVal.begin(), NewRetVal.end());
  }

  return RetVal;
}

bool printIt = false;

std::set<ReservationSite*> ReserveTM::ReserveTMPass::CompressionSitesValue(Instruction *instr, ValueSet values, bool store, InstructionSet& visited, bool skip, bool initial) {
  ReservationSiteSet RetVal;
  InstructionSet willReserveVisited = visited;
  auto inserted = visited.insert(instr);
  if (!inserted.second) {
    ++num_compression_aborts_from_recursion;
    return RetVal;
  }

  // Out of transactional scope
  if (fAnalyzedInstructions.find(instr) == fAnalyzedInstructions.end()) {
    ++num_compression_aborts_from_exit;
    return RetVal;
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
      auto Site = (*entry).second;

      if (!store && Site->containsLoadFrom(values)) {
        RetVal.insert(Site);
        return RetVal;
      }

      if (Site->containsStoreTo(values)) {
        RetVal.insert(Site);
        return RetVal;
      }
    }
  }

  if (!skip) {
    if (CallInst* ci = dyn_cast<CallInst>(instr)) {
      InstructionSet willReserveVisited = visited;
      RetVal = willReserveValue(ci, values, store, willReserveVisited);
      if (!RetVal.empty()) {
        return RetVal;
      }
    }
  }

  auto preds = getPrevious(instr);
  for (auto pred : preds) {
    auto block = instr->getParent();
    auto func = block->getParent();

    ValueSet new_values = values;
    if (getFirstInstruction(func) == instr) {
      CallInst* ci = dyn_cast<CallInst>(pred);
      //DEBUG_WITH_TYPE("compress", errs() << "Moving to callSite Instruction: " << ci << "\n");
      for (auto value : values) {
        if (Argument *arg = dyn_cast<Argument>(value)) {
          if (arg->getParent() == func) {
            auto fv = ci->getArgOperand(arg->getArgNo());
            if (Constant *c = dyn_cast<Constant>(fv)) {
              if (c->isNullValue()) {
                //TODO: handle?
                //RetVal.insert(c);
                continue;
              }
            }
            auto peers = AliasMapper::getPeers(fv);
            new_values.insert(peers.begin(), peers.end());
          }
        }
      }
    }

    auto ret = CompressionSitesValue(pred, new_values, store, visited, true);
    if (ret.empty()) {
      if (!RetVal.empty())
        ++num_compression_aborts_from_partial_paths;

      RetVal.clear();
      return RetVal;
    } else {
      RetVal.insert(ret.begin(), ret.end());
    }
  }

  return RetVal;
}

std::set<ReservationSite*> ReserveTM::ReserveTMPass::compressStoreIntoLoad(Instruction *instr, ValueSet values, InstructionSet& visited, bool skip, bool initial) {
  ReservationSiteSet RetVal;
  InstructionSet willReserveVisited = visited;
  auto inserted = visited.insert(instr);
  if (!inserted.second) {
 //   ++num_compression_aborts_from_recursion;
    return RetVal;
  }

  // Out of transactional scope
  if (fAnalyzedInstructions.find(instr) == fAnalyzedInstructions.end()) {
   // ++num_compression_aborts_from_exit;
    return RetVal;
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
      auto Site = (*entry).second;

      if (Site->containsLoadFrom(values)) {
        RetVal.insert(Site);
        return RetVal;
      }

      //TODO: might need to handle this
#if 0
      if (Site->containsStoreTo(values)) {
        RetVal.insert(Site);
        return RetVal;
      }
#endif
      return RetVal;
    }
  }

  //TODO: need to evntually handle this
  if (!skip) {
#if 0
    if (CallInst* ci = dyn_cast<CallInst>(instr)) {
      InstructionSet willReserveVisited = visited;
      RetVal = willReserveValue(ci, values, store, willReserveVisited);
      if (!RetVal.empty()) {
        return RetVal;
      }
    }
#endif
    return RetVal;
  }

  auto preds = getPrevious(instr, true);
  for (auto pred : preds) {
    auto block = instr->getParent();
    auto func = block->getParent();

    ValueSet new_values = values;
    if (getFirstInstruction(func) == instr) {
      CallInst* ci = dyn_cast<CallInst>(pred);
      //DEBUG_WITH_TYPE("compress", errs() << "Moving to callSite Instruction: " << ci << "\n");
      for (auto value : values) {
        if (Argument *arg = dyn_cast<Argument>(value)) {
          if (arg->getParent() == func) {
            auto fv = ci->getArgOperand(arg->getArgNo());
            if (Constant *c = dyn_cast<Constant>(fv)) {
              if (c->isNullValue()) {
                //TODO: handle?
                //RetVal.insert(c);
                continue;
              }
            }
            auto peers = AliasMapper::getPeers(fv);
            new_values.insert(peers.begin(), peers.end());
          }
        }
      }
    }

    auto ret = compressStoreIntoLoad(pred, new_values, visited, true);
    if (ret.empty()) {
      //if (!RetVal.empty())
      //  ++num_compression_aborts_from_partial_paths;

      RetVal.clear();
      return RetVal;
    } else {
      RetVal.insert(ret.begin(), ret.end());
    }
  }

  assert(RetVal.size() <= 1);

  return RetVal;
}

bool ReserveTM::ReserveTMPass::compressSite(InstructionMap::const_iterator entry) {
  auto instr = (*entry).first;
  auto Site = (*entry).second;

  assert (Site && !Site->empty());

  ValueSet aliases;
  InstructionSet visited;
  auto value = Site->getValue();

  auto type = Site->getType();
  if ((type != ReservationSite::LOAD) && (type != ReservationSite::STORE)) {
    return false;
  }

  ++num_compression_attempted;
  ReservationSiteSet CompressionSites;
  bool ThreadLocal = false;
  bool Store = (type == ReservationSite::STORE);
  if (Store) {
    aliases.insert(value);
    CompressionSites = compressStoreIntoLoad(instr, aliases, visited, true, true);
    if (CompressionSites.size()) {
      ++num_compression_succeeded_simple;
      Site->compressWithPreviousStore(value);
      Function *func = Site->Instr->getParent()->getParent();
      DEBUG_WITH_TYPE("compress", errs() << "Compressing Store: (");
      DEBUG_WITH_TYPE("compress", (func->hasName() ? (errs().write_escaped(func->getName())) : (errs() << "*NONE*\n")));
      DEBUG_WITH_TYPE("compress", errs() << "): " << *(Site->Instr) << " with " << CompressionSites.size() << " reservation site(s):\n");
      for (auto CompressionSite : CompressionSites) {
        Instruction *v = CompressionSite->Instr;
        func = CompressionSite->Instr->getParent()->getParent();
        DEBUG_WITH_TYPE("compress", errs() << "CompressionSite: (");
        DEBUG_WITH_TYPE("compress", (func->hasName() ? (errs().write_escaped(func->getName())) : (errs() << "*NONE*\n")));
        DEBUG_WITH_TYPE("compress", errs() << "): " << *v << "\n");
        auto entry = fReservationSiteMap.find(CompressionSite->Instr);
        assert (entry != fReservationSiteMap.end());
        auto NewSite = new ReservationSite(CompressionSite->Instr, CompressionSite->Val, ReservationSite::STORE, false);
        NewSite->tx = CompressionSite->tx;
        entry->second = NewSite;
        return true;
      }
    }
    aliases.clear();
    visited.clear();
  }
#if 0
  if (isFromAlloc(value)) {
    ThreadLocal = true;
    CompressionSites = SUCCESS_INTRA_PROCEDURAL;
  } else {
#endif
    //TODO: use peers?
    aliases.insert(value);
    //auto aliases = AliasMapper::getPeers(value);
    CompressionSites = CompressionSitesValue(instr, aliases, Store, visited, true, true);
#if 0
  }
#endif

  if (CompressionSites.size()) {
    if (Store) {
      ++num_stores_compressed;
      //TODO: fix stat
      //if (CompressionSites == SUCCESS_INTER_PROCEDURAL)
      //++num_stores_compressed_inter_procedurally;
      if (ThreadLocal)
        ++num_stores_compressed_thread_local;
      Site->compressWithPreviousStore(value);
      Function *func = Site->Instr->getParent()->getParent();
      DEBUG_WITH_TYPE("compress", errs() << "Compressing Store: (");
      DEBUG_WITH_TYPE("compress", (func->hasName() ? (errs().write_escaped(func->getName())) : (errs() << "*NONE*\n")));
      DEBUG_WITH_TYPE("compress", errs() << "): " << *(Site->Instr) << " with " << CompressionSites.size() << " reservation site(s):\n");
      for (auto Site : CompressionSites) {
        Instruction *v = Site->Instr;
        func = Site->Instr->getParent()->getParent();
        DEBUG_WITH_TYPE("compress", errs() << "Site: (");
        DEBUG_WITH_TYPE("compress", (func->hasName() ? (errs().write_escaped(func->getName())) : (errs() << "*NONE*\n")));
        DEBUG_WITH_TYPE("compress", errs() << "): " << *v << "\n");
      }
    } else {
      ++num_loads_compressed;
      //TODO: fix stat
      //if (CompressionSites == SUCCESS_INTER_PROCEDURAL)
      //++num_loads_compressed_inter_procedurally;
      if (ThreadLocal)
        ++num_loads_compressed_thread_local;
      Site->compressWithPreviousLoad(value);
      Function *func = Site->Instr->getParent()->getParent();
      DEBUG_WITH_TYPE("compress", errs() << "Compressing Load: (");
      DEBUG_WITH_TYPE("compress", (func->hasName() ? (errs().write_escaped(func->getName())) : (errs() << "*NONE*\n")));
      DEBUG_WITH_TYPE("compress", errs() << "): " << *(Site->Instr) << " with " << CompressionSites.size() << " reservation site(s):\n");
      for (auto Site : CompressionSites) {
        Instruction *v = Site->Instr;
        func = Site->Instr->getParent()->getParent();
        DEBUG_WITH_TYPE("compress", errs() << "Site: (");
        DEBUG_WITH_TYPE("compress", (func->hasName() ? (errs().write_escaped(func->getName())) : (errs() << "*NONE*\n")));
        DEBUG_WITH_TYPE("compress", errs() << "): " << *v << "\n");
      }
    }

    DEBUG_WITH_TYPE("compress", errs() << "Instruction: " << instr << " completely compressed\n");
    ++num_compression_succeeded;

    return true;
  }

  return false;
}

bool ReserveTM::ReserveTMPass::eliminateLoads(InstructionMap::const_iterator entry, ValueSet& cachedEliminations, ValueSet& cachedNonEliminations) {
  auto instr = (*entry).first;
  auto Site = (*entry).second;

  DEBUG_WITH_TYPE("eliminate", errs() << "Elimination Processing for Instruction: " << instr << "\n");

  assert(Site);

  assert(!Site->empty());

  size_t size = Site->size();

  Value* V = Site->getValue();
  auto type = Site->getType();
  if (type == ReservationSite::STORE) {
    auto Allocs = isFromAlloc(V);
    if (!Allocs.empty()) {
      ++num_stores_eliminated_thread_local;
      Site->compressWithPreviousStore(V);

      DEBUG_WITH_TYPE("eliminate", errs() << "Instruction (Store): " << instr << " completely eliminated\n");
      ++num_eliminated_stores;

      return true;
    }
  } else if (type == ReservationSite::LOAD) {
    auto Allocs = isFromAlloc(V);
    if (!Allocs.empty()) {
      ++num_loads_eliminated_thread_local;
      Site->compressWithPreviousLoad(V);
      DEBUG_WITH_TYPE("eliminate", errs() << "Instruction (Load): " << instr << " completely eliminated\n");
      ++num_eliminated_loads;

      return true;
    }
#if 0
    bool aliasesAreAlwaysFromAlloc = false;
    ValueSet aliases;
    if (cachedEliminations.find(V) == cachedEliminations.end()) {
      if (cachedNonEliminations.find(V) == cachedNonEliminations.end()) {
        if (!AliasMapper::getAliases(V, aliases)) {
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
          Site->compressWithPreviousLoad(V);
          aliasesAreAlwaysFromAlloc = true;
        }
      }
    }

#endif
    else if (getenv("RESERVETM_STRONG_ISOLATION"))
    {
      bool canEliminate = true;
      ValueSet aliases;
      if (cachedEliminations.find(V) == cachedEliminations.end()) {
        if (cachedNonEliminations.find(V) != cachedNonEliminations.end()) {
          canEliminate = false;
        } else {
          if (!AliasMapper::getAliases(V, aliases)) {
            canEliminate = false; 
          } else {
            //TODO: is this right?
            for (auto it : fReservationSiteMap) {
              auto bb_Site = it.second;
              assert(bb_Site);

              if (bb_Site->empty())
                continue;

              if (bb_Site->containsStoreTo(aliases)) {
                canEliminate = false;
                break;
              }
            }
          }
        }
      }

      if (canEliminate) {
        if (printAliasEliminate) {
          DEBUG_WITH_TYPE("eliminate", errs() << "At: " << instr << " want to get rid of: " << *V << "\n");

          if (aliases.size() > 1) {
            DEBUG_WITH_TYPE("eliminate", errs() << "Aliases:\n");
            DEBUG_WITH_TYPE("eliminate", printValues(aliases));
          } else if (aliases.size() == 0) {
            DEBUG_WITH_TYPE("eliminate", errs() << "Using cached result\n");
          }

        }

        Site->compressWithPreviousLoad(V);
        DEBUG_WITH_TYPE("eliminate", errs() << "Instruction (Load): " << instr << " completely eliminated\n");
        ++num_eliminated_loads;

        cachedEliminations.insert(aliases.begin(), aliases.end());

        return true;
      } else {
        cachedNonEliminations.insert(aliases.begin(), aliases.end());
      }
    }
  }

  return false; 
}

std::set<ReservationSite*> ReserveTM::ReserveTMPass::canMergeValue(Instruction* instr, Value* value, InstructionSet& visited, bool initial) {
  ReservationSiteSet RetVal;
  auto inserted = visited.insert(instr);
  if (!inserted.second)
    return RetVal;

  if (!initial) {
    //TODO: this is only valid if the funciton has absolutely no reservations
    if (CallInst* ci = dyn_cast<CallInst>(instr)) {
      auto it = fFunctionCalls.find(ci);
      if (it != fFunctionCalls.end())
        return RetVal;
    }

    if (instr == value) {
      if (getenv("RESERVETM_DISABLE_MOVE")) {
        return RetVal;
      }
      auto NewInstr = moveUp(instr);
      if (NewInstr) {
        ++num_merge_definition_moves;
        DEBUG_WITH_TYPE("merge", errs() << "Merge processing moved Instr: (" << *instr << ") before Intr: (" << *NewInstr << ")\n");
        visited.erase(inserted.first);
        return canMergeValue(NewInstr, value, visited, initial);
      } else {
        ++num_merge_aborts_from_definition;
      }
      return RetVal;
    }

    auto it = fReservationSiteMap.find(instr);
    if (it != fReservationSiteMap.end()) {
      auto Site = it->second;

      assert(Site);

      if (Site->size()) {
        RetVal.insert(Site);
        return RetVal;
      }
    }
  }

  CompressionResult canMerge = FAIL;
  // First try within the block
  auto preds = getPrevious(instr, true);
  for (auto pred : preds) {
    RetVal = canMergeValue(pred, value, visited);
    return RetVal;
  }

  // TODO: cross block traffic
#if 0
  preds = getPrevious(instr);
  for (auto pred : preds) {
    auto block = instr->getParent();
    auto func = block->getParent();

    auto fv = value;
    if (getFirstInstruction(func) == instr) {
      ++num_merge_aborts_from_function_calls;
      return FAIL;

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
    } else {
      auto PredBlock = pred->getParent();
      for (succ_iterator si = succ_begin(PredBlock), si_e = succ_end(PredBlock); si != si_e; ++si) {
        BasicBlock *succ = *si;

        if (succ != block) {
          DEBUG_WITH_TYPE("merge", errs() << "Merge Processing stopped due to partial path at Instr: " << *instr << "\n");
          ++num_merge_aborts_from_partial_paths;
          return FAIL;
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
#endif

  return RetVal;
}

bool ReserveTM::ReserveTMPass::mergeBlock(InstructionMap::const_iterator entry, std::queue<InstructionMap::const_iterator>& mergeQueue) {
  auto instr = (*entry).first;
  auto Site = (*entry).second;

  DEBUG_WITH_TYPE("merge", errs() << "Merge Processing for Instr: " << *instr << "\n");
  //TODO: need to stop on defining instance
  //TODO: need to stop when at the highest transaction

  assert(Site && !Site->empty());

  size_t size = Site->size();
  auto num_entries = Site->numOrderedLoadsStores();
  Value * args[num_entries];
  uint32_t bit_vector = Site->copyLoadsStores(args);
  InstructionSet visited;

  for (auto it = args; it != args+num_entries; ++it) {
    Value *value = *it;
    bool store = bit_vector & 1;
    bit_vector = bit_vector >> 1;

    visited.clear();
    auto MergeSites = canMergeValue(instr, value, visited, true);

    if (MergeSites.empty())
      break;

    if (store) {
      ++num_stores_merged;
      //TODO: fix stat
      //if (canMerge == SUCCESS_INTER_PROCEDURAL)
      //  ++num_stores_merged_inter_procedurally;
      Site->compressWithPreviousStore(value);
    } else {
      ++num_loads_merged;
      //TODO: fix stat
      //if (canMerge == SUCCESS_INTER_PROCEDURAL)
      //  ++num_loads_merged_inter_procedurally;
      Site->compressWithPreviousLoad(value);
    }

    for (auto MergeSite : MergeSites) {
      DEBUG_WITH_TYPE("merge", errs() << "Merged site at Instr: (" << *instr << " (" << instr->getParent()->getParent()->getName().str() << ")" << ") into site at Intr: (" << *MergeSite->Instr << " (" << MergeSite->Instr->getParent()->getParent()->getName().str() << ")" << ")\n");
      if (store)
        MergeSite->insertStore(value);
      else
        MergeSite->insertLoad(value);
    }
  }

  if (Site->empty()) {
    DEBUG_WITH_TYPE("merge", errs() << "Instruction: " << instr << " completely merged\n");
    ++num_reservation_sites_completely_merged;
    return true;
  }

  if (Site->size() != size)
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
    auto Site = it->second;
    if (Site && !Site->empty()) {
      ++instrs;
      reads += Site->numReads();
      writes += Site->numWrites();
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
        start = NULL;
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
  llvm::Statistic *num_stm_reserve[MAX_RESERVATIONS];
  std::queue<Function *> funcQueue;
  FunctionSet fAdded;

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
#if 0
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
#endif

#if 0
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
#endif
  AliasMapper::analyzeModule(M);

  ValueSet aliases;
  for (auto instr : fFunctionPointerBlocks) {
    aliases.clear();

    CallInst* ci = dyn_cast<CallInst>(instr);

    assert(AliasMapper::getAliases(ci->getCalledValue(), aliases) && (aliases.size() > 1));

#if 0
    DEBUG_WITH_TYPE("func", errs() << "Function Pointer at: " << block << " (" << *ci->getCalledValue() << ") has " << aliases.size() << " aliases\n");
    if (aliases.size() > 1) {
      DEBUG_WITH_TYPE("func", errs() << "Aliases:\n");
      DEBUG_WITH_TYPE("func", printValues(aliases));
    }
#endif
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
    auto Site = (*entry).second;
    assert(Site);

    if (Site->empty())
      continue;

    if (!getenv("RESERVETM_ELIMINATE") || !eliminateLoads(entry, cachedEliminations, cachedNonEliminations))
      compressionQueue.push(entry);
  }

  // Compression Pass
  std::queue<InstructionMap::const_iterator> mergeQueue;
  while (!compressionQueue.empty()) {
    auto entry = compressionQueue.front();
    compressionQueue.pop();
    if (!getenv("RESERVETM_COMPRESS") || !compressSite(entry))
      mergeQueue.push(entry);
  }

  // Merge Pass
  while (!mergeQueue.empty()) {
    auto entry = mergeQueue.front();
    mergeQueue.pop();

    //if (singleWriter && hasPreviousStore(entry))
    //	++num_reservation_sites_with_previous_store;

    if (getenv("RESERVETM_MERGE")) //&& (num_reservation_sites_completely_merged < atoi(getenv("MAX_MERGES"))))
      mergeBlock(entry, mergeQueue);
  }

  //Analyze Pass
  InstructionSet visited;
  int index = 0;
  for (auto entry : fReservationSiteMap) {
    auto Site = entry.second;

    assert(Site);

    if (Site->empty())
      continue;


    visited.clear();
#if 1
    auto instr = entry.first;
    uint32_t reads = 0;
    uint32_t writes = 0;
    uint32_t instrs = 0;
    if (calcReadsWrites(instr->getParent(), &instrs, &reads, &writes, visited, instr)) {
      Site->setUpcomingInstructions(instrs);
      Site->setUpcomingReads(reads);
      Site->setUpcomingWrites(writes);
      if (instrs == 0)
        ++num_reservation_sites_at_end;
    } else
#endif
    {
      Site->setUpcomingInstructions(1000+index);
      Site->setUpcomingReads(10000+index);
      Site->setUpcomingWrites(10000+index);
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
          auto Site = (*found_it).second;

          assert(Site);

          if (!Site->empty()) {
            ++num_functions_instrumented;
            break;
          }
        }
      }
    }
  }

  stm_reserve[0] = dyn_cast<Function>(M.getOrInsertFunction("stmreserve01",
      Type::getInt32Ty(M.getContext()),
      txType,
      Type::getInt32Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt32Ty(M.getContext()),
      Type::getInt32Ty(M.getContext()),
      Type::getInt32Ty(M.getContext()),
      NULL));
  num_stm_reserve[0] = &num_stm_reserve_1;
  stm_reserve[1] = dyn_cast<Function>(M.getOrInsertFunction("stmreserve02",
      Type::getInt32Ty(M.getContext()),
      txType,
      Type::getInt32Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt32Ty(M.getContext()),
      Type::getInt32Ty(M.getContext()),
      Type::getInt32Ty(M.getContext()),
      NULL));
  num_stm_reserve[1] = &num_stm_reserve_2;
  stm_reserve[2] = dyn_cast<Function>(M.getOrInsertFunction("stmreserve03",
      Type::getInt32Ty(M.getContext()),
      txType,
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
      Type::getInt32Ty(M.getContext()),
      txType,
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
  stm_reserve[4] = dyn_cast<Function>(M.getOrInsertFunction("stmreserve05",
      Type::getInt32Ty(M.getContext()),
      txType,
      Type::getInt32Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt32Ty(M.getContext()),
      Type::getInt32Ty(M.getContext()),
      Type::getInt32Ty(M.getContext()),
      NULL));
  num_stm_reserve[4] = &num_stm_reserve_5;
  stm_reserve[5] = dyn_cast<Function>(M.getOrInsertFunction("stmreserve06",
      Type::getInt32Ty(M.getContext()),
      txType,
      Type::getInt32Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt32Ty(M.getContext()),
      Type::getInt32Ty(M.getContext()),
      Type::getInt32Ty(M.getContext()),
      NULL));
  num_stm_reserve[5] = &num_stm_reserve_6;
  stm_reserve[6] = dyn_cast<Function>(M.getOrInsertFunction("stmreserve07",
      Type::getInt32Ty(M.getContext()),
      txType,
      Type::getInt32Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt64Ty(M.getContext()),
      Type::getInt32Ty(M.getContext()),
      Type::getInt32Ty(M.getContext()),
      Type::getInt32Ty(M.getContext()),
      NULL));
  num_stm_reserve[6] = &num_stm_reserve_7;

  // Instrument Pass
  for (auto entry : fReservationSiteMap) {
    auto Site = entry.second;

    assert(Site);

    if (!Site->size())
      continue;

    auto instr = entry.first;
    auto num_entries = Site->numOrderedLoadsStores();
    if (num_entries > 0) {
      assert(num_entries <= MAX_RESERVATIONS);

      DEBUG_WITH_TYPE("instrument", errs() << "Instrumenting Instruction: " << instr << " ");
      DEBUG_WITH_TYPE("instrument", Site->debugPrint());

      Value * args[num_entries + 5];
      uint32_t bit_vector = Site->copyLoadsStores(args + 2);

      for (auto i = 2; i <= num_entries+1; ++i) {
        args[i] = CastInst::CreatePointerCast (args[i], Type::getInt64Ty(args[i]->getContext()), "", instr);
      }
      args[0] = Site->tx;
      args[1] = ConstantInt::get(IntegerType::get(M.getContext(), 32), bit_vector, true);
      unsigned cur_entry = num_entries + 2;
      args[cur_entry++] = ConstantInt::get(IntegerType::get(M.getContext(), 32), num_entries, true);
      args[cur_entry++] = ConstantInt::get(IntegerType::get(M.getContext(), 32), Site->upcomingReads(), true);
      args[cur_entry++] = ConstantInt::get(IntegerType::get(M.getContext(), 32), Site->upcomingWrites(), true);
      CallInst::Create(stm_reserve[num_entries - 1], ArrayRef<Value*>(args, num_entries + 5), "", instr);

      ++(*num_stm_reserve[num_entries - 1]);
      ++num_reservation_sites_instrumented;
    } else {
      ++num_reservation_sites_skipped;
    }
  }

  return true;
}
