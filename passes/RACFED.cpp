#include "ASPIS.h"
#include "Utils/Utils.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <random>

#define INIT_SIGNATURE                                                         \
  -0xDEAD // The same value has to be used as initializer for the signatures in
          // the code
#define INTRA_FUNCTION_CFC 0 // Default to 0 if not defined

#define MARTI_DEBUG true

using namespace llvm;

/**
 * initializeBlockSignatures
1:for all Basic Block (BB) in CFG do
2: repeat compileTimeSig ← random number
3: until compileTimeSig is unique
4: repeat subRanPrevVal ← random number
5: until (compileTimeSig + subRanP revV al) is unique
 * updateSignatureRandom
6:for all BB in CFG do
7:   if NrInstrBB > 2 then
8:    for all original instructions insert after
9:      signature ← signature + random number
  * checkCompileTimeSigAtJump
10:for all BB in CFG insert at beginning
11:  signature ← signature − subRanPrevVal
12:  if signature != compileTimeSig error()
13:for all BB in CFG do
  * checkRetVal
14: if Last Instr. is return instr. and NrIntrBB > 1 then
15:   Calculate needed variables
16:     return Val ← random number
17:     adjust Value ← (compileTimeSigBB + Sum{in%2 = load i32, ptr @signature, align 4
18:                 return Val
19:   Insert signature update before return instr.
20:     signature ← signature + adjustValue
21:     if signature != returnVal error()
22: else
  * checkJump
23:   for all Successor of BB do
24:    adjustValue ← (compileTimeSigBB + \Sum{instrMonUpdates}) -
25:     (compileTimeSigsuccs + subRanPrevValsuccs)
26:   Insert signature update at BB end
27:     signature ← signature + adjustValue
*/


// --- INITIALIZE BLOCKS RANDOM ---

bool isNotUniqueCompileTimeSig(
  const uint32_t bb_num,
  const std::unordered_map<BasicBlock*, uint32_t> &compileTimeSig
) {
  for (const auto &[_, other_bb_id] : compileTimeSig) {
    if ( other_bb_id == bb_num ) return true;
  }
  return false;
}

bool isNotUnique(
  const uint32_t current_id,
  const std::unordered_map<BasicBlock*, uint32_t> &RandomNumBBs,
  const std::unordered_map<BasicBlock*, uint32_t> &SubRanPrevVals
) {
  for (const auto &[other_bb, other_bb_num] : RandomNumBBs) {
    uint32_t other_id = static_cast<uint32_t>(other_bb_num) + SubRanPrevVals.at(other_bb);
    if ( other_id == current_id ) {
      return true;
    }
  }

  return false;
}

void RACFED::initializeBlocksSignatures(Module &Md, Function &Fn) {
  std::mt19937 rng(0xB00BA5); // seed fisso per riproducibilità
  std::uniform_int_distribution<uint32_t> dist(1, 0x7fffffff);
  uint32_t randomBB;
  uint32_t randomSub;

  for (BasicBlock &BB : Fn) {
    do {
      randomBB = dist(rng);
    } while ( isNotUniqueCompileTimeSig(randomBB, compileTimeSig) );

    do {
      randomSub = dist(rng);
    } while ( isNotUnique(
      static_cast<uint32_t>(randomBB) + randomSub,
      compileTimeSig,
      subRanPrevVals) );

    compileTimeSig.insert(std::pair(&BB, randomBB));
    subRanPrevVals.insert(std::pair(&BB, randomSub));
  }
}


// --- UPDATE SIGNATURE RANDOM  ---

void originalInstruction(BasicBlock &BB, std::vector<Instruction*> &OrigInstructions) {
  for (Instruction &I : BB) {
    if (isa<PHINode>(&I)) continue; // NON è originale
    if (I.isTerminator()) continue; // NON è originale
    if (isa<DbgInfoIntrinsic>(&I)) continue; // debug, ignora OrigInstructions.push_back(&I);
    OrigInstructions.push_back(&I);
  }
}

void RACFED::updateCompileSigRandom(Module &Md, Function &Fn, 
				    GlobalVariable *RuntimeSigGV, 
				    Type *IntType) {
  std::mt19937 rng(0xC0FFEE); // seed fisso per riproducibilità
  std::uniform_int_distribution<uint32_t> dist(1, 0x7fffffff);

  for (auto &BB: Fn){
    std::vector<Instruction*> OrigInstructions;
    originalInstruction(BB, OrigInstructions);

    if (OrigInstructions.size() <= 2) continue;

    uint64_t partial_sum;

    for (Instruction *I : OrigInstructions) {
      Instruction *InsertPt = nullptr;

      // Non puoi inserire "dopo" un terminator: inserisci prima del terminator stesso
      if (I->isTerminator()) {
        InsertPt = I; // insert BEFORE terminator
      } else {
        InsertPt = I->getNextNode(); // insert BEFORE next instruction (equivale a "dopo I")
      }

      IRBuilder<> B(InsertPt);

      // signature = signature + randomConstant
      uint64_t K = dist(rng);

      try {
        partial_sum = K + sumIntraInstruction.at(&BB);
      } catch (std::out_of_range &) {
        partial_sum = K;
      }

      sumIntraInstruction.insert(std::pair(&BB, partial_sum));

      Value *OldSig = B.CreateLoad(IntType, RuntimeSigGV);
      Value *Add = B.CreateAdd(OldSig, ConstantInt::get(IntType, K), "sig_add");
      B.CreateStore(Add, RuntimeSigGV);
    }
  }

}

// --- CHECK BLOCKS AT JUMP END ---

void RACFED::checkCompileTimeSigAtJump(Module &Md, Function &Fn, 
				       GlobalVariable *RuntimeSigGV, Type *IntType) {
  BasicBlock *ErrBB = BasicBlock::Create(Fn.getContext(), "ErrBB", &Fn);
  IRBuilder<> ErrB(ErrBB);

  IRBuilder<> B(&*(Fn.front().getFirstInsertionPt()));

  for(BasicBlock &BB: Fn) {
    int randomNumberBB = compileTimeSig.find(&BB)->second;
    int subRanPrevVal = subRanPrevVals.find(&BB)->second;
 
    // in this case BB is not the first Basic Block of the function, so it has to
    // update RuntimeSig and check it
    if (!BB.isEntryBlock()) {
      if (isa<LandingPadInst>(BB.getFirstNonPHI()) ||
	  BB.getName().contains_insensitive("verification")) {
	IRBuilder<> BChecker(&*BB.getFirstInsertionPt());
	BChecker.CreateStore(llvm::ConstantInt::get(IntType, randomNumberBB),
			     RuntimeSigGV, true);
      } else if (!BB.getName().contains_insensitive("errbb")) {
	BasicBlock *NewBB = BasicBlock::Create(
	    BB.getContext(), "RACFED_Verification_BB", BB.getParent(), &BB);
	IRBuilder<> BChecker(NewBB);

	// add instructions for the first runtime signature update
	Value *InstrRuntimeSig = BChecker.CreateLoad(IntType, RuntimeSigGV, true);

	Value *RuntimeSignatureVal = BChecker.CreateSub(
	    InstrRuntimeSig, llvm::ConstantInt::get(IntType, subRanPrevVal));
	BChecker.CreateStore(RuntimeSignatureVal, RuntimeSigGV, true);

	// update phi placing them in the new block
	while (isa<PHINode>(&BB.front())) {
	  Instruction *PhiInst = &BB.front();
	  PhiInst->removeFromParent();
	  PhiInst->insertBefore(&NewBB->front());
	}

	// replace the uses of BB with NewBB
	for (BasicBlock &BB_ : *BB.getParent()) {
	  if (&BB_ != NewBB) {
	    BB_.getTerminator()->replaceSuccessorWith(&BB, NewBB);
	  }
	}

	// add instructions for checking the runtime signature
	Value *CmpVal =
	    BChecker.CreateCmp(llvm::CmpInst::ICMP_EQ, RuntimeSignatureVal,
			       llvm::ConstantInt::get(IntType, randomNumberBB));
	BChecker.CreateCondBr(CmpVal, &BB, ErrBB);

	// add NewBB and BB into the NewBBs map
	NewBBs.insert(std::pair<BasicBlock *, BasicBlock *>(NewBB, &BB));
      }
    }
  }
}

// --- UPDATE BRANCH SIGNATURE BEFORE JUMP ---

ConstantInt* expectedSignature(
	BasicBlock *Succ, Module &Md,
	const std::unordered_map<BasicBlock *, uint32_t> &compileTimeSig,
	const std::unordered_map<BasicBlock *, uint32_t> &subRanPrevVals
) {
  const int expected = compileTimeSig.at(Succ);
  const int expectedSub = subRanPrevVals.at(Succ);
  auto *I32 = Type::getInt32Ty(Md.getContext());
  return ConstantInt:: get(I32, expected+expectedSub);
}

void RACFED::checkBranches(Module &Md,  GlobalVariable *RuntimeSigGV,
			   Type *IntType,	IRBuilder<> B, BasicBlock &BB) {
  Instruction *Term = BB.getTerminator();
  auto *BI = dyn_cast<BranchInst>(Term);
  if (!BI) return;

  //load the current runtimevariable
  Value *Current = B.CreateLoad(IntType, RuntimeSigGV, "current");
  Value *Expected = nullptr;

//define if conditional or unconditional branch
  //Conditional: expected= CT_succ+subRan_succ
    //adj = CTB-exp--> new signature = RT -adj
  if (BI -> isUnconditional()) {
      BasicBlock *Succ = BI->getSuccessor(0);
      auto expected = expectedSignature(Succ,Md,compileTimeSig,subRanPrevVals);
     // adj = expected - current
      Value *Adj = B.CreateSub(Expected, Current, "racfed.adj");
      Value *NewSig = B.CreateAdd(Current, Adj, "racfed.newsig");
      B.CreateStore(NewSig, RuntimeSigGV);

      // verify newSig == expected
      Value *Ok = B.CreateICmpEQ(NewSig, Expected, "racfed.ok");

      // Replace terminator with condbr(ok, succ, ErrBB)
      BI->eraseFromParent();
      IRBuilder<> BT(&BB);
      BT.CreateCondBr(Ok, Succ, nullptr);
  } else {
      BasicBlock *SuccT = BI->getSuccessor(0);
      BasicBlock *SuccF = BI->getSuccessor(1);
  }
}

//Conditional: compute the two adj and the signature that corresponds.
//
// void RACFED::createCFGVerificationBB(
//     BasicBlock &BB, std::unordered_map<BasicBlock *, int> &RandomNumberBBs,
//     std::unordered_map<BasicBlock *, int> &SubRanPrevVals, Value &RuntimeSig,
//     Value &RetSig, BasicBlock &ErrBB
// ) {
//
//   // checkCompileSigAtJump() NON ENTRY BLOCK
//   // compileTimeSig - subRunPrevVal
//   // if compileTimeSig != runtime_sig error()
//
//   auto *IntType = llvm::Type::getInt64Ty(BB.getContext());
//
//   int randomNumberBB = RandomNumberBBs.find(&BB)->second;
//   int subRanPrevVal = SubRanPrevVals.find(&BB)->second;
//
//
//   // checkReturnVal()
//   // compute returnValue
//   // compute adjValue
//   // runtime_sig = runtime_sig + adjValue
//
//
//   // checkBranchJump()
//   // compute adjValue
//   // runtime_sig = runtime_sig + adjValue
//
//   // update the signature for the successors
//   int randomNumberBB_succ;
//   int subRanPrevVal_succ;
//
//   Instruction *Term = BB.getTerminator();
//   int successors = Term->getNumSuccessors();
//
//   for (int i = 0; i < successors; i++) {
//     BasicBlock *Succ = Term->getSuccessor(i);
//     if (!Succ->getName().contains_insensitive("errbb")) {
//       randomNumberBB_succ = RandomNumberBBs.find(Succ)->second;
//       subRanPrevVal_succ = randomNumberBB - randomNumberBB_succ;
//
//       // update the map
//       if (SubRanPrevVals.find(Succ)->second == 1) {
//         SubRanPrevVals.erase(Succ);
//         SubRanPrevVals.insert(
//             std::pair<BasicBlock *, int>(Succ, subRanPrevVal_succ));
//       } else {
//         // if the successor has already been visited, we have to check if the
//         // signature is consistent
//         if (SubRanPrevVals.find(Succ)->second != subRanPrevVal_succ) {
//           // if not, we have to update the signature
//           int diff = subRanPrevVal_succ - SubRanPrevVals.find(Succ)->second;
//           IRBuilder<> B(&*BB.getFirstInsertionPt());
//           if (isa<BranchInst>(Term) &&
//               cast<BranchInst>(Term)->isConditional()) {
//             // if the terminator is a conditional branch, we have to update the
//             // signature only if the condition is true or false, depending on
//             // the successor
//             B.SetInsertPoint(Term);
//           } else {
//             B.SetInsertPoint(Term);
//           }
//
//         }
//       }
//     }
//   }
//
//   Handle return instructions
//   if (isa<ReturnInst>(Term)) {
//     BasicBlock *RetVerificationBB = BasicBlock::Create(
//         BB.getContext(), "RACFED_ret_Verification_BB", BB.getParent(), &BB);
//     // Move instructions from BB to RetVerificationBB, except the verification
//     // logic we just added? No, we want to verify BEFORE return. Actually, the
//     // verification block is already added at the beginning of BB. Now we want
//     // to update signature before return? RASM updates signature at exit?
//
//
//
//     IRBuilder<> BRet(RetVerificationBB);
//     Value *InstrRuntimeSig = BRet.CreateLoad(IntType, &RuntimeSig, true);
//     Value *InstrRetSig = BRet.CreateLoad(IntType, &RetSig, true);
//
//     // In RASM/RACFED, we might check if RuntimeSig matches RetSig (or some
//     // derived value) at return. For now, let's just check if they are
//     // consistent. But RetSig is initialized to RandomNumberBBs.size() +
//     // currSig.
//
//     // Let's stick to the basic block verification for now.
//   }
// }


PreservedAnalyses RACFED::run(Module &Md, ModuleAnalysisManager &AM) {
  // mappa: istruzione originale -> random r usato per S = S + r
  std::unordered_map<llvm::Instruction*, int> InstrUpdates;
  auto *I64 = llvm::Type::getInt64Ty(Md.getContext());
  auto *I32 = llvm::Type::getInt32Ty(Md.getContext());
  std::unordered_map<Function*, BasicBlock*> ErrBBs;

  GlobalVariable *RuntimeSig = Md.getNamedGlobal("signature");
  if (!RuntimeSig) {
    RuntimeSig = new GlobalVariable(
        Md,
        I64,
        /*isConstant=*/false,
        GlobalValue::ExternalLinkage,
        ConstantInt::get(I64, 0),
        "signature");
  }

  // createFtFuncs(Md);
  getFuncAnnotations(Md, FuncAnnotations);
  LinkageMap linkageMap = mapFunctionLinkageNames((Md));

  for (Function &Fn : Md) {
    if (shouldCompile(Fn, FuncAnnotations))
      initializeBlocksSignatures(Md, Fn);
  }

  for (Function &Fn: Md) {
    updateCompileSigRandom(Md, Fn, RuntimeSig, I64);
  }

  for(Function &Fn: Md) {
    checkCompileTimeSigAtJump(Md, Fn, RuntimeSig, I64);
  }

  // createCFGVerificationBB();
  //
  // for (Function &Fn : Md) {
  //   if (!shouldCompile(Fn, FuncAnnotations))
  //     continue;
  //
  //   if (shouldCompile(Fn, FuncAnnotations)) {
  //     DebugLoc debugLoc;
  //     for (auto &I : Fn.front()) {
  //       if (I.getDebugLoc()) {
  //         debugLoc = I.getDebugLoc();
  //         break;
  //       }
  //     }
  // }
  return PreservedAnalyses::all();
}

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK

llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "RACFED", "v0.1", [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, ModulePassManager &MPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "racfed-verify") {
                    MPM.addPass(RACFED());
                    return true;
                  }
                  return false;
                });
          }};
}

// -- UNUSED FUNCTIONS --

// void RACFED::splitBBsAtCalls(Module &Md) {
//   for (Function &Fn : Md) {
//     if (shouldCompile(Fn, FuncAnnotations)) {
//       std::vector<CallBase *> CallInsts;
//       for (BasicBlock &BB : Fn) {
//         for (Instruction &I : BB) {
//           if (isa<CallBase>(&I) && !isa<IntrinsicInst>(&I)) {
//             CallInsts.push_back(cast<CallBase>(&I));
//           }
//         }
//       }
//
//       for (CallBase *Call : CallInsts) {
//         if (Call->getParent()->getTerminator() != Call) {
//           SplitBlock(Call->getParent(), Call->getNextNode());
//         }
//       }
//     }
//   }
// }
//
// CallBase *RACFED::isCallBB(BasicBlock &BB) {
//   for (Instruction &I : BB) {
//     if (isa<CallBase>(&I) && !isa<IntrinsicInst>(&I)) {
//       return cast<CallBase>(&I);
//     }
//   }
//   return nullptr;
// }
//
// void RACFED::initializeEntryBlocksMap(Module &Md) {
//   // Implementation for INTRA_FUNCTION_CFC == 1, left empty for now as we
//   // default to 0
// }
//
// Value *RACFED::getCondition(Instruction &I) {
//   // Helper to get condition from terminator if it's a branch
//   if (BranchInst *BI = dyn_cast<BranchInst>(&I)) {
//     if (BI->isConditional()) {
//       return BI->getCondition();
//     }
//   }
//   return nullptr;
// }
