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
  * create CFG
  * checkBeginning
10:for all BB in CFG insert at beginning
11:  signature ← signature − subRanPrevVal
12:  if signature != compileTimeSig error()
13:for all BB in CFG do
  * checkRetVal
14: if Last Instr. is return instr. and NrIntrBB > 1 then
15:   Calculate needed variables
16:     return Val ← random number
17:     adjust Value ← (compileTimeSigBB + Sum{instrMonUpdates}) -
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
  const int bb_num,
  const std::unordered_map<BasicBlock*, int> &compileTimeSig
) {
  for (const auto &pair : compileTimeSig) {
    if (pair.second == bb_num) return true;
  }
  return false;
}

bool isNotUnique(
  const int bb_num, const int subrun_num,
  const std::unordered_map<BasicBlock*, int> &RandomNumBBs,
  const std::unordered_map<BasicBlock*, int> &SubRanPrevVals
) {

  for (const auto &pair : RandomNumBBs) {
    if (pair.second + SubRanPrevVals.at(pair.first) == bb_num + subrun_num) {
      return true;
    }
  }

  return false;
}

void RACFED::initializeBlocksSignatures(Module &Md) {
  int i = 0;
  srand(static_cast<unsigned>(time(nullptr)));   // compileTimeSig weak random generator
  int randomBB;
  int randomSub;

  for (Function &Fn : Md) {
    if (shouldCompile(Fn, FuncAnnotations)) {
      for (BasicBlock &BB : Fn) {

        do {
          randomBB = rand();
        } while (isNotUniqueCompileTimeSig(randomBB, compileTimeSig));

        do {
          randomSub = rand();
        } while (isNotUnique(i, randomSub, compileTimeSig, subRanPrevVals));

        compileTimeSig.insert(std::pair(&BB, randomBB));//not random, guarantees unicity
        subRanPrevVals.insert(std::pair(&BB, randomSub)); //In this way the sub value is random
        sumIntraInstruction.insert(std::pair(&BB, 0));//assign value to the sum of the instr
        i++;

      }
    }
  }
}


// --- UPDATE SIGNATURE RANDOM  ---
void originalInstruction(BasicBlock &BB,  std::vector<Instruction*> &OrigInstructions) {

  for (Instruction &I : BB) {
    if (isa<PHINode>(&I)) continue; // NON è originale
    if (I.isTerminator()) continue; // NON è originale
    if (isa<DbgInfoIntrinsic>(&I)) continue; // debug, ignora OrigInstructions.push_back(&I);
    OrigInstructions.push_back(&I);
  }
}

void RACFED::updateCompileSigRandom(Function &F, Module &Md) {
  LLVMContext &Ctx = Md.getContext();
  GlobalVariable *SigGV = Md.getNamedGlobal("signature");
  std::mt19937 rng(0xC0FFEE); // seed fisso per riproducibilità
  std::uniform_int_distribution<uint32_t> dist(1, 0x7fffffff);
  auto *I32 = Type::getInt32Ty(Ctx);
  if (!SigGV) {
    SigGV = new GlobalVariable(
        Md,
        I32,
        /*isConstant=*/false,
        GlobalValue::ExternalLinkage,
        ConstantInt::get(I32, 0),
        "signature");
  }

  for (auto &BB: F){
    std::vector<Instruction*> OrigInstructions;
    originalInstruction(BB, OrigInstructions);

    if (OrigInstructions.size() <= 2)
      continue;

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
      uint32_t K = dist(rng);

      try {
        partial_sum = K + sumIntraInstruction.at(&BB);
      } catch (std::out_of_range &) {
        partial_sum = K;
      }

      sumIntraInstruction.insert(std::pair(&BB, partial_sum));

      Value *OldSig = B.CreateLoad(I32, SigGV);
      Value *Add = B.CreateAdd(OldSig, ConstantInt::get(I32, K), "sig_add");
      B.CreateStore(Add, SigGV);
    }
  }
}

// --- CREATE CFG VERIFICATION ---



void RACFED::createCFGVerificationBB(
    BasicBlock &BB, std::unordered_map<BasicBlock *, int> &RandomNumberBBs,
    std::unordered_map<BasicBlock *, int> &SubRanPrevVals, Value &RuntimeSig,
    Value &RetSig, BasicBlock &ErrBB
) {

  // checkBeginning() NON ENTRY BLOCK
  // compileTimeSig - subRunPrevVal
  // if compileTimeSig != runtime_sig error()

  auto *IntType = llvm::Type::getInt32Ty(BB.getContext());

  int randomNumberBB = RandomNumberBBs.find(&BB)->second;
  int subRanPrevVal = SubRanPrevVals.find(&BB)->second;

  // in this case BB is not the first Basic Block of the function, so it has to
  // update RuntimeSig and check it
  if (!BB.isEntryBlock()) {
    if (isa<LandingPadInst>(BB.getFirstNonPHI()) ||
        BB.getName().contains_insensitive("verification")) {
      IRBuilder<> BChecker(&*BB.getFirstInsertionPt());
      BChecker.CreateStore(llvm::ConstantInt::get(IntType, randomNumberBB),
                           &RuntimeSig, true);
    } else if (!BB.getName().contains_insensitive("errbb")) {
      BasicBlock *NewBB = BasicBlock::Create(
          BB.getContext(), "RACFED_Verification_BB", BB.getParent(), &BB);
      IRBuilder<> BChecker(NewBB);

      // add instructions for the first runtime signature update
      Value *InstrRuntimeSig = BChecker.CreateLoad(IntType, &RuntimeSig, true);

      Value *RuntimeSignatureVal = BChecker.CreateSub(
          InstrRuntimeSig, llvm::ConstantInt::get(IntType, subRanPrevVal));
      BChecker.CreateStore(RuntimeSignatureVal, &RuntimeSig, true);

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
      BChecker.CreateCondBr(CmpVal, &BB, &ErrBB);

      // add NewBB and BB into the NewBBs map
      NewBBs.insert(std::pair<BasicBlock *, BasicBlock *>(NewBB, &BB));
    }
  }

  // checkReturnVal()
  // compute returnValue
  // compute adjValue
  // runtime_sig = runtime_sig + adjValue


  // checkBranchJump()
  // compute adjValue
  // runtime_sig = runtime_sig + adjValue

  // update the signature for the successors
  int randomNumberBB_succ;
  int subRanPrevVal_succ;

  Instruction *Term = BB.getTerminator();
  int successors = Term->getNumSuccessors();

  for (int i = 0; i < successors; i++) {
    BasicBlock *Succ = Term->getSuccessor(i);
    if (!Succ->getName().contains_insensitive("errbb")) {
      randomNumberBB_succ = RandomNumberBBs.find(Succ)->second;
      subRanPrevVal_succ = randomNumberBB - randomNumberBB_succ;

      // update the map
      if (SubRanPrevVals.find(Succ)->second == 1) {
        SubRanPrevVals.erase(Succ);
        SubRanPrevVals.insert(
            std::pair<BasicBlock *, int>(Succ, subRanPrevVal_succ));
      } else {
        // if the successor has already been visited, we have to check if the
        // signature is consistent
        if (SubRanPrevVals.find(Succ)->second != subRanPrevVal_succ) {
          // if not, we have to update the signature
          int diff = subRanPrevVal_succ - SubRanPrevVals.find(Succ)->second;
          IRBuilder<> B(&*BB.getFirstInsertionPt());
          if (isa<BranchInst>(Term) &&
              cast<BranchInst>(Term)->isConditional()) {
            // if the terminator is a conditional branch, we have to update the
            // signature only if the condition is true or false, depending on
            // the successor
            B.SetInsertPoint(Term);
          } else {
            B.SetInsertPoint(Term);
          }

        }
      }
    }
  }

  // Handle return instructions
  // if (isa<ReturnInst>(Term)) {
  //   BasicBlock *RetVerificationBB = BasicBlock::Create(
  //       BB.getContext(), "RACFED_ret_Verification_BB", BB.getParent(), &BB);
  //   // Move instructions from BB to RetVerificationBB, except the verification
  //   // logic we just added? No, we want to verify BEFORE return. Actually, the
  //   // verification block is already added at the beginning of BB. Now we want
  //   // to update signature before return? RASM updates signature at exit?
  //
  //
  //
  //   IRBuilder<> BRet(RetVerificationBB);
  //   Value *InstrRuntimeSig = BRet.CreateLoad(IntType, &RuntimeSig, true);
  //   Value *InstrRetSig = BRet.CreateLoad(IntType, &RetSig, true);
  //
  //   // In RASM/RACFED, we might check if RuntimeSig matches RetSig (or some
  //   // derived value) at return. For now, let's just check if they are
  //   // consistent. But RetSig is initialized to RandomNumberBBs.size() +
  //   // currSig.
  //
  //   // Let's stick to the basic block verification for now.
  // }
}

PreservedAnalyses RACFED::run(Module &Md, ModuleAnalysisManager &AM) {
  // mappa: istruzione originale -> random r usato per S = S + r
  std::unordered_map<llvm::Instruction*, int> InstrUpdates;
  auto *IntType = llvm::Type::getInt32Ty(Md.getContext());
  std::unordered_map<Function*, BasicBlock*> ErrBBs;

  // createFtFuncs(Md);
  getFuncAnnotations(Md, FuncAnnotations);
  LinkageMap linkageMap = mapFunctionLinkageNames((Md));

  initializeBlocksSignatures(Md);

  for (Function &F: Md){
    updateCompileSigRandom(F, Md);
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