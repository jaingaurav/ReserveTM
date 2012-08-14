#include "AliasMapper.h"
#include "llvm/Support/Casting.h"
#include "llvm/Constant.h"
#include "llvm/Support/Debug.h"


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

using namespace llvm;
using ReserveTM::ValueSet;

bool printAlias = false;

bool sameOffset(GetElementPtrInst *a, GetElementPtrInst *b) {
    if (a->getPointerOperandType() != b->getPointerOperandType())
        return false;

    auto a_it = a->idx_begin();
    auto b_it = b->idx_begin();
    while (a_it != a->idx_end() && b_it != b->idx_end()) {
        if (*a_it != *b_it) {
            return false;
        }
        ++a_it;
        ++b_it;
    }

    while (a_it != a->idx_end()) {
        if (*a_it != 0) {
            return false;
        }
        ++a_it;
    }

    while (b_it != b->idx_end()) {
        if (*b_it != 0) {
            return false;
        }
        ++b_it;
    }

    return true;
}

std::map<Value *, ReserveTM::AliasMapperRelation*> fAliasMap;
ReserveTM::BasicBlockSet fAnalyzedBlocks;
std::multimap<Function *, CallInst *> ReserveTM::AliasMapper::fFunctionCallSites;

bool functionIsValid(Function *func) {
    if (!func->isIntrinsic()
        && func->hasName()
        && (func->getName().str().find("_ZN3stm") == std::string::npos)
        && (func->getName().str().find("_assert") == std::string::npos)) {
        return true;
    }

    return false;
}

void ReserveTM::AliasMapper::analyzeModule(llvm::Module &M) {
    for (auto i = M.begin(), ie = M.end(); i != ie; ++i) {
        auto func = i;
        if (functionIsValid(func) && func->size()) {
            /*
            DEBUG_WITH_TYPE("analyze", errs() << "============================================================================\n");
            DEBUG_WITH_TYPE("analyze", errs() << "Alias Analyzing Function: ");
            DEBUG_WITH_TYPE("analyze", (func->hasName() ? (errs().write_escaped(func->getName()) << "\n") : (errs() << "*NONE*\n")));
            DEBUG_WITH_TYPE("analyze", errs() << "============================================================================\n");
*/
            analyzeBlock(&func->getEntryBlock());
        }
    }

    for (auto entry : fFunctionCallSites) {
        auto called = entry.first;
        auto ci = entry.second;

        /*
           if (called->hasName()
           && (called->getName().str().find("_ZN10comparatorC1EPFlPKvS1_EPFlPN3stm8TxThreadES1_S1_E") != std::string::npos)) {
           called = entry.first;
           }*/

        auto internal_arg = called->arg_begin();
        for (unsigned arg_num = 0; arg_num < ci->getNumArgOperands(); ++arg_num, ++internal_arg) {
            Value* fv = ci->getArgOperand(arg_num);
            if (Constant *c = dyn_cast<Constant>(fv)) {
                if (c->isNullValue()) {
                    continue;
                }
                //TODO: pointer constants?
            }
            aliasValues(internal_arg, fv);
        }

        for (inst_iterator I = inst_begin(called), E = inst_end(called); I != E; ++I) {
            if (ReturnInst* ri = dyn_cast<ReturnInst>(&*I)) {
                Value * rv = ri->getReturnValue();
                if (rv)
                    aliasValues(ci, rv);
            }
        }
    }

    /*
     * TODO handle aliasing of function pointer args
     */
}

void ReserveTM::AliasMapper::analyzeBlock(BasicBlock *const block) {
    if (fAnalyzedBlocks.find(block) == fAnalyzedBlocks.end()) {
        fAnalyzedBlocks.insert(block);

        for (auto instr_i = block->begin(), instr_e = block->end(); instr_i != instr_e; ++instr_i) {
            if (LoadInst *li = dyn_cast<LoadInst>(&*instr_i)) {
                aliasLoad(li->getPointerOperand(), li);
            } else if (StoreInst *si = dyn_cast<StoreInst>(&*instr_i)) {
                aliasStore(si->getValueOperand(), si->getPointerOperand());
            } else if (CallInst *ci = dyn_cast<CallInst>(&*instr_i)) {
                Function* called = ci->getCalledFunction();
                if (!called || !called->isIntrinsic()) {
                    if (called
                        && called->hasName()
                        && ((called->getName().str().find("stm_read") != std::string::npos)
                            || (called->getName().str().find("stm_write") != std::string::npos)
                            || (called->getName().str().find("tx_alloc") != std::string::npos)
                            || (called->getName().str().find("tx_free") != std::string::npos))) {
                        if (called->getName().str().find("tx_alloc") != std::string::npos) {
                        } else {
                            Value *arg = ci->getArgOperand(0);
                            if (Constant *c = dyn_cast<Constant>(arg)) {
                                if (c->isNullValue()) {
                                    continue;
                                }
                            } else if (arg->getType()->isPointerTy()) {
                                if (called->getName().str().find("stm_read") != std::string::npos) {
                                    aliasLoad(arg, ci);
                                } else if (called->getName().str().find("stm_write") != std::string::npos) {
                                    aliasStore(arg, ci);
                                } else if (called->getName().str().find("tx_free") != std::string::npos) {
                                }
                            }
                        }
                    } else {
                        if (called) {
                            if (!called->isIntrinsic()
                                && called->hasName()
                                && (called->getName().str().find("_ZN3stm") == std::string::npos)
                                && (called->getName().str().find("_assert") == std::string::npos)
                                && called->size()) {
                                fFunctionCallSites.insert(std::pair<Function*,CallInst*>(called, ci));
                            }
                        } else {
                            //fFunctionPointerBlocks.insert(block);
                        }
                    }
                }
                //TODO splitting is not a great idea
            } else if (CastInst *ci = dyn_cast<CastInst>(&*instr_i)) {
                aliasValues(ci, ci->getOperand(0));
            } else if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(&*instr_i)) {
                //TODO: need to manage offsets
                aliasOffsetValues(gep->getPointerOperand(), gep, gep);
            } else if (CmpInst *si = dyn_cast<CmpInst>(&*instr_i)) {
            } else if (SelectInst *si = dyn_cast<SelectInst>(&*instr_i)) {
                aliasValues(si->getTrueValue(), si);
                aliasValues(si->getFalseValue(), si);
            } else if (PHINode* phiNode = dyn_cast<PHINode>(&*instr_i)) {
                for (auto i = 0; i < phiNode->getNumIncomingValues(); ++i) {
                    aliasValues(phiNode->getIncomingValue(i), phiNode);
                }
            } else if (isa<AllocaInst>(&*instr_i)
                || isa<BinaryOperator>(&*instr_i)) {
            } else if (AtomicRMWInst *ci = dyn_cast<AtomicRMWInst>(&*instr_i)) {
                //aliasValues(ci->getPointerOperand(), ci);
            } else if (AtomicCmpXchgInst *ci = dyn_cast<AtomicCmpXchgInst>(&*instr_i)) {
                //aliasValues(ci->getPointerOperand(), ci);
                aliasValues(ci->getPointerOperand(), ci->getNewValOperand());
            } else if (isa<TerminatorInst>(&*instr_i)) {
            } else if (isa<LandingPadInst>(&*instr_i)) {
            } else if (isa<InsertValueInst>(&*instr_i)) {
            } else if (isa<ExtractValueInst>(&*instr_i)) {
                //TODO: need to handle this
            } else {
                DEBUG_WITH_TYPE("alias", errs() << "Unhandled instruction: " << *instr_i << "\n");
                //assert(false);
            }
        }

        for (succ_iterator si = succ_begin(block), si_e = succ_end(block); si != si_e; ++si) {
            BasicBlock *succ = *si;
            //errs() << "Compressing pred: " << pred << "\n";
            analyzeBlock(succ);
        }
    }
}

ReserveTM::AliasMapperRelation* ReserveTM::AliasMapper::getAliasSet(Value *a) {
    auto a_it = fAliasMap.find(a);
    if (fAliasMap.end() == a_it) {
        AliasMapperRelation* myset = new AliasMapperRelation(a);
        myset->fAliases.insert(a);
        fAliasMap[a] = myset;

        return myset;
    }

    return a_it->second;
}

void ReserveTM::AliasMapper::aliasValues(Value *a, Value* b) {
    if (a != b) {
        //if (!isa<Constant>(a) && !isa<Constant>(b)) {
        if (printAlias)
            DEBUG_WITH_TYPE("alias", errs() << "Adding alias for " << *a << " to: " << *b << "\n");
        auto a_set = getAliasSet(a);
        a_set->fAliases.insert(b);
        auto b_set = getAliasSet(b);
        b_set->fAliases.insert(a);
        //}
    }
}

void ReserveTM::AliasMapper::aliasOffsetValues(Value *parent, Value* child, GetElementPtrInst * gep) {
    if (!isa<Constant>(parent) && !isa<Constant>(child)) {
        if (printAlias)
            DEBUG_WITH_TYPE("alias", errs() << "Adding gep alias for parent: " << *parent << " to child: " << *child << " with: " << *gep << "\n");
        auto parent_set = getAliasSet(parent);
        parent_set->fOffsetChildren.insert(std::pair<GetElementPtrInst*,Value*>(gep, child));
        auto child_set = getAliasSet(child);

        assert(child_set->fOffsetParent == 0);
        assert(child_set->fOffsetParentOffset == 0);

        child_set->fOffsetParent = parent;
        child_set->fOffsetParentOffset = gep;
    }
}

void ReserveTM::AliasMapper::aliasLoad(Value* src, Value* dst) {
    if (!isa<Constant>(src) && !isa<Constant>(dst)) {
        if (printAlias)
            DEBUG_WITH_TYPE("alias", errs() << "Adding load alias for src: " << *src << " to dst: " << *dst << "\n");
        auto src_set = getAliasSet(src);
        auto dst_set = getAliasSet(dst);

        assert(dst_set->fLoadedFrom == 0);

        dst_set->fLoadedFrom = src;
        src_set->fLoadedBy.insert(dst);
    }
}

void ReserveTM::AliasMapper::aliasStore(Value* src, Value* dst) {
    if (!isa<Constant>(src) && !isa<Constant>(dst)) {
        if (printAlias)
            DEBUG_WITH_TYPE("alias", errs() << "Adding store alias for src: " << *src << " to dst: " << *dst << "\n");
        auto src_set = getAliasSet(src);
        auto dst_set = getAliasSet(dst);
        dst_set->fStoredFrom.insert(src);
        src_set->fStoredInto.insert(dst);
    }
}

ValueSet ReserveTM::AliasMapper::getPeers(Value* v) {
    ValueSet retVal;
    retVal.insert(v);

    auto as = getAliasSet(v);

    if (as->fOffsetParent) {
        auto peers = getPeers(as->fOffsetParent);

        for (auto peer : peers) {
            auto offsetFromSet = getAliasSet(peer);

            for (auto entry : offsetFromSet->fOffsetChildren) {
                auto gep = entry.first;
                auto offsetChild = entry.second;

                if (sameOffset(as->fOffsetParentOffset, gep)) {
                    auto ins = retVal.insert(offsetChild);
                }
            }
        }
    }

    return retVal;
}

//TODO: use move operator
bool ReserveTM::AliasMapper::getAliases(Value *v, ValueSet& aliases) {
    if (printAlias)
        DEBUG_WITH_TYPE("alias", errs() << "START! = Trying to find aliases of " << *v << "\n");

    std::set<AliasMapperRelation *> visited;
    std::set<AliasMapperRelation *> errors;
    if (!getAliasSet(v)->getAliases(aliases, visited, errors))
        return false;

    visited.clear();

    if (printAlias) {
        DEBUG_WITH_TYPE("alias", errs() << "END! = Got " << aliases.size() << " aliases for : " << *v << "\n");
        /*if (aliases.size() > 1) {
          DEBUG_WITH_TYPE("alias", printValues(aliases));
          DEBUG_WITH_TYPE("alias", errs() << "EOF\n");
          }*/
    }

    return true;
}

Function* getFunction(Value * value) {
    if (Instruction *I  = dyn_cast<Instruction>(value)) {
        return I->getParent()->getParent();
    } else if (Argument *arg = dyn_cast<Argument>(value)) {
        return arg->getParent();
    }
    return 0;
}

bool ReserveTM::AliasMapperRelation::getAliases(ValueSet& aliases, std::set<AliasMapperRelation *>& visited, std::set<AliasMapperRelation *>& errors) {
    auto inserted = visited.insert(this);
    if (inserted.second) {
        if (printAlias)
            DEBUG_WITH_TYPE("alias", errs() << "Working on: " << *(this->me) << "(" << this << ")" << " with fAliases.size() == " << fAliases.size() << "\n");
        int count = 0;
        for (auto alias : fAliases) {
            if (printAlias) {
                DEBUG_WITH_TYPE("alias", errs() << "Working on: " << count++ << " of " << *(this->me) << "(" << this << ")" << "which is: " << *alias << "(");
                DEBUG_WITH_TYPE("alias", errs().write_escaped(getFunction(alias)->getName()));
                DEBUG_WITH_TYPE("alias", errs() << ")\n");
            }
            auto ins = aliases.insert(alias);
            auto as = AliasMapper::getAliasSet(alias);
            if (errors.find(as) != errors.end())
                return false;

            if (ins.second && printAlias) {
                DEBUG_WITH_TYPE("alias", errs() << "Adding root alias for " << *(this->me) << "(" << this << ")" << "(" << as << ") as: " << *alias << "(");
                DEBUG_WITH_TYPE("alias", errs().write_escaped(getFunction(alias)->getName()));
                DEBUG_WITH_TYPE("alias", errs() << ")\n");
            }
            /*DEBUG_WITH_TYPE("alias", errs() << "END! = Got " << as->fAliases.size() << " aliases for : " << *alias << "\n");
              if (as->fAliases.size() > 1) {
              DEBUG_WITH_TYPE("alias", printValues(as->fAliases));
              DEBUG_WITH_TYPE("alias", errs() << "EOF\n");
              }*/
            if (!as->getAliases(aliases, visited, errors))
                return false;
        }

                /*
         * If this value is loaded from a value lets get all the aliases of values that it's loaded from
         */
        if (fLoadedFrom) {
            auto loadedFromSet = AliasMapper::getAliasSet(fLoadedFrom);
            if (errors.find(loadedFromSet) != errors.end())
                return false;

            ValueSet loadedFromAliases;
            std::set<AliasMapperRelation *> new_visited;
            std::set<AliasMapperRelation *> new_errors = errors;
            new_errors.insert(visited.begin(), visited.end());
            if (printAlias)
                DEBUG_WITH_TYPE("alias", errs() << "Loads of " << *(this->me) << "(" << this << ")" << " are " << loadedFromSet << "\n");
            loadedFromSet->getAliases(loadedFromAliases, new_visited, new_errors);
            for (auto loadedFromAlias : loadedFromAliases) {
                auto alias_set = AliasMapper::getAliasSet(loadedFromAlias);
                /*
                 * Other values that are loaded from this value are in the alias set
                 */
                for (auto loadedBy : alias_set->fLoadedBy) {
                    auto ins = aliases.insert(loadedBy);
                    if (ins.second && printAlias) {
                        DEBUG_WITH_TYPE("alias", errs() << "Adding loaded alias for " << *(this->me) << "(" << this << ")" << " as: " << *loadedBy << "(");
                        DEBUG_WITH_TYPE("alias", errs().write_escaped(getFunction(loadedBy)->getName()));
                        DEBUG_WITH_TYPE("alias", errs() << ")\n");
                    }
                    if (!AliasMapper::getAliasSet(loadedBy)->getAliases(aliases, visited, errors))
                        return false;
                }
                /*
                 * Other values stored into this value are aliases
                 */
                for (auto storedFrom : alias_set->fStoredFrom) {
                    auto ins = aliases.insert(storedFrom);
                    if (ins.second && printAlias) {
                        DEBUG_WITH_TYPE("alias", errs() << "Adding stored alias for " << *(this->me) << "(" << this << ")" << " as: " << *storedFrom << "(");
                        DEBUG_WITH_TYPE("alias", errs().write_escaped(getFunction(storedFrom)->getName()));
                        DEBUG_WITH_TYPE("alias", errs() << ")\n");
                    }
                    if (!AliasMapper::getAliasSet(storedFrom)->getAliases(aliases, visited, errors))
                        return false;
                }
            }
        }

        /*
         * If this value is stored into any value lets get all the aliases of values that it's stored into
         */
        ValueSet storedIntoAliases;
        for (auto storedInto : fStoredInto) {
            auto storedIntoSet = AliasMapper::getAliasSet(storedInto);
            if (errors.find(storedIntoSet) != errors.end())
                return false;

            storedIntoAliases.clear();
            std::set<AliasMapperRelation *> new_visited;
            std::set<AliasMapperRelation *> new_errors = errors;
            new_errors.insert(visited.begin(), visited.end());
            if (printAlias)
                DEBUG_WITH_TYPE("alias", errs() << "Set " << *(this->me) << "(" << this << ")" << " is stored into by " << storedIntoSet << "\n");
            storedIntoSet->getAliases(storedIntoAliases, new_visited, new_errors);
            for (auto storedIntoAlias : storedIntoAliases) {
                auto alias_set = AliasMapper::getAliasSet(storedIntoAlias);
                /*
                 * If the stored value is loaded by anyone, that is an alias
                 */
                if (alias_set->fLoadedFrom) {
                    auto ins = aliases.insert(alias_set->fLoadedFrom);
                    if (ins.second && printAlias) {
                        DEBUG_WITH_TYPE("alias", errs() << "Adding stored alias for " << *(this->me) << "(" << this << ")" << " as: " << *alias_set->fLoadedFrom << "(");
                        DEBUG_WITH_TYPE("alias", errs().write_escaped(getFunction(alias_set->fLoadedFrom)->getName()));
                        DEBUG_WITH_TYPE("alias", errs() << ")\n");
                    }
                    if (!AliasMapper::getAliasSet(alias_set->fLoadedFrom)->getAliases(aliases, visited, errors))
                        return false;
                }
            }
        }

        if (fOffsetParent) {
            for (auto entry : fAliasMap) {
                auto as = entry.second;
                if (as->fOffsetParent) {
                    if (sameOffset(as->fOffsetParentOffset, fOffsetParentOffset)) {
                        auto alias = entry.first;
                        if (printAlias)
                            DEBUG_WITH_TYPE("alias", errs() << "Working on offset alias of " << this << " which is: " << *alias << "\n");
                        auto ins = aliases.insert(alias);
                        auto alias_as = AliasMapper::getAliasSet(alias);
                        if (errors.find(alias_as) != errors.end())
                            return false;

                        if (ins.second && printAlias) {
                            DEBUG_WITH_TYPE("alias", errs() << "Adding offset alias for " << this << "(" << alias_as << ") as: " << *alias << "(");
                            DEBUG_WITH_TYPE("alias", errs().write_escaped(getFunction(alias)->getName()));
                            DEBUG_WITH_TYPE("alias", errs() << ")\n");
                        }
                        /*DEBUG_WITH_TYPE("alias", errs() << "END! = Got " << as->fAliases.size() << " aliases for : " << *alias << "\n");
                          if (as->fAliases.size() > 1) {
                          DEBUG_WITH_TYPE("alias", printValues(as->fAliases));
                          DEBUG_WITH_TYPE("alias", errs() << "EOF\n");
                          }*/
                        if (!alias_as->getAliases(aliases, visited, errors))
                            return false;
                    }
                }
            }
        }

    }

    return true;
}


