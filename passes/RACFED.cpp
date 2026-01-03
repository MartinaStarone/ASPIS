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
#define GAMBA_DEBUG false

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
17:     adjust Value ← (compileTimeSigBB + SumIntraInstructions) -
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

std::uniform_int_distribution<uint32_t> dist32(1, 0x7fffffff);
std::uniform_int_distribution<uint64_t> dist64(1, 0xffffffff);
std::mt19937 rng64(0x5EED00); // seed fisso per riproducibilità

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
  uint32_t randomBB;
  uint32_t randomSub;

  for (BasicBlock &BB : Fn) {
    do {
      randomBB = dist32(rng);
    } while ( isNotUniqueCompileTimeSig(randomBB, compileTimeSig) );

    do {
      randomSub = dist32(rng);
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

  for (auto &BB: Fn){
    std::vector<Instruction*> OrigInstructions;
    originalInstruction(BB, OrigInstructions);

    if (OrigInstructions.size() <= 2) continue;

    uint64_t partial_sum = 0;

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
      uint64_t K = dist32(rng);
      partial_sum += K;
      #if GAMBA_DEBUG
      errs() << "Value of K: " << K << "\n";
      errs() << "Value of partial_sum: " << partial_sum << "\n"; 
      errs() << "Value of sumIntra: " << sumIntraInstruction[&BB] << "\n";
      #endif
      Value *Sig = B.CreateLoad(IntType, RuntimeSigGV);
      Value *NewSig = B.CreateAdd(Sig, ConstantInt::get(IntType, K), "sig_add");
      B.CreateStore(NewSig, RuntimeSigGV);
      sumIntraInstruction[&BB] = partial_sum;
    }
  }
}

// --- CHECK BLOCKS AT JUMP END ---
// FIXME: Check this function to comply with the decisions made in design
//
// FIXME: Fix warnings
void RACFED::checkCompileTimeSigAtJump(Module &Md, Function &Fn, BasicBlock &BB,
				       GlobalVariable *RuntimeSigGV, Type *IntType,
				       BasicBlock &ErrBB) {
  if( BB.isEntryBlock() ) return;

  // in this case BB is not the first Basic Block of the function, so it has
  // to update RuntimeSig and check it
  Instruction *FirstNonPHI = BB.getFirstNonPHI();
  if ( (FirstNonPHI && isa<LandingPadInst>(FirstNonPHI)) ||
     BB.getName().contains_insensitive("verification") ) {

    if (BB.getFirstInsertionPt() == BB.end()) return; // Skip empty/invalid blocks

    int randomNumberBB = compileTimeSig.find(&BB)->second;
    IRBuilder<> BChecker(&*BB.getFirstInsertionPt());
    BChecker.CreateStore(llvm::ConstantInt::get(IntType, randomNumberBB), RuntimeSigGV, true);
  } else if (!BB.getName().contains_insensitive("errbb")) {
    int randomNumberBB = compileTimeSig.find(&BB)->second;
    int subRanPrevVal = subRanPrevVals.find(&BB)->second;
    BasicBlock *NewBB = BasicBlock::Create(
    BB.getContext(), "RACFED_Verification_BB", BB.getParent(), &BB);
    IRBuilder<> BChecker(NewBB);

    // add instructions for the first runtime signature update
    Value *InstrRuntimeSig =
    BChecker.CreateLoad(IntType, RuntimeSigGV, true);

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
    BB.replaceAllUsesWith(NewBB);

    // add instructions for checking the runtime signature
    Value *CmpVal =
    BChecker.CreateCmp(llvm::CmpInst::ICMP_EQ, RuntimeSignatureVal,
		       llvm::ConstantInt::get(IntType, randomNumberBB));
    BChecker.CreateCondBr(CmpVal, &BB, &ErrBB);

    // add NewBB and BB into the NewBBs map
    NewBBs.insert(std::pair<BasicBlock *, BasicBlock *>(NewBB, &BB));
  }
}

// --- UPDATE BRANCH SIGNATURE BEFORE JUMP ---
Constant* expectedSignature(
	BasicBlock *Succ, Type *IntType,
	const std::unordered_map<BasicBlock *, uint32_t> &compileTimeSig,
	const std::unordered_map<BasicBlock *, uint32_t> &subRanPrevVals
) {
  const int expected = compileTimeSig.at(Succ);
  const int expectedSub = subRanPrevVals.at(Succ);
  return ConstantInt::get(IntType, expected+expectedSub);
}
/*
* checkJump
23:   for all Successor of BB do
24:    adjustValue ← (compileTimeSigBB + \Sum{instrMonUpdates}) -
25:     (compileTimeSigsuccs + subRanPrevValsuccs)
26:   Insert signature update at BB end
27:     signature ← signature + adjustValue
*/
void RACFED::checkBranches(Module &Md, BasicBlock &BB,  GlobalVariable *RuntimeSigGV,
			   Type *IntType, BasicBlock &ErrBB) {
  Instruction *Term = BB.getTerminator();
  IRBuilder<> B(&BB);
  auto *BI = dyn_cast<BranchInst>(Term);
  if (!BI) return;


  //define if conditional or unconditional branch
  //Conditional: expected= CT_succ+subRan_succ
  //adj = CTB-exp--> new signature = RT -adj
  if ( BI->isUnconditional() ) { // only one successor
      //load the current runtimevariable
      Value *Current = B.CreateLoad(IntType, RuntimeSigGV, "current");
      BasicBlock *Succ = BI->getSuccessor(0);
      auto expected = expectedSignature(Succ,IntType,compileTimeSig,subRanPrevVals);
      // adj = expected - current
      Value *Adj = B.CreateSub(expected, Current, "racfed_adj");
      Value *NewSig = B.CreateAdd(Current, Adj, "racfed_newsig");
      B.CreateStore(NewSig, RuntimeSigGV);

      // verify newSig == expected
      Value *Ok = B.CreateICmpEQ(NewSig, expected, "racfed_ok");

      // Replace terminator with condbr(ok, succ, ErrBB)
      BI->eraseFromParent();
      IRBuilder<> BT(&BB);
      BT.CreateCondBr(Ok, Succ, &ErrBB);
  } else {
      BasicBlock *SuccT = BI->getSuccessor(0);
      BasicBlock *SuccF = BI->getSuccessor(1);
  }
}


// --- CHECK RETURN UPDATE VALUE ---
// checkRetVal:
//
// 14: if Last Instr. is return instr. and NrIntrBB > 1 then
// 15:   Calculate needed variables
// 16:     returnVal ← random number
// 17:     adjustValue ← (compileTimeSigBB + Sum) -
// 18:                 returnVal
// 19:   Insert signature update before return instr.
// 20:     signature ← signature + adjustValue
// 21:     if signature != returnVal error()
void RACFED::checkReturnValue(Module &Md, Function &Fn, BasicBlock &BB,
			      GlobalVariable *RuntimeSigGV, 
			      Type* IntType, BasicBlock &ErrBB,
			      Value *BckupRunSig) {
  Instruction *Term = BB.getTerminator();

  if( !isa<ReturnInst>(Term) ) return;

  std::vector<Instruction*> org_instr;
  originalInstruction(BB, org_instr);
  if( org_instr.size() <= 2 ) return;

  // Splits the BB that contains the return instruction into
  // two basic blocks:
  // BB will contain the return instruction
  // BeforeRetBB will contain all of the instructions before the return one
  //
  // These two BBs will be linked meaning that BeforeRetBB->successor == BB
  BasicBlock *BeforeRetBB = BB.splitBasicBlockBefore(Term);

  // Creating control basic block to insert before
  // the return instruction
  BasicBlock *ControlBB = BasicBlock::Create(
    Md.getContext(), 
    "RAFCED_ret_verification_BB", 
    &Fn,
    &BB
  );

  // Relinking the basic blocks so that the structure 
  // results in: BeforeRetBB->ControlBB->BB
  BeforeRetBB->getTerminator()->replaceSuccessorWith(&BB, ControlBB);

  // Inserting instructions into ControlBB
  IRBuilder<> B(ControlBB);
  // 15:   Calculate needed variables
  // 16:     returnVal ← random number
  // 17:     adjustValue ← (compileTimeSigBB + Sum) -
  // 18:                 returnVal
  uint64_t random_ret_value = dist64(rng64);
  // This is a 64 bit SIGNED integer (cause a subtraction happens
  // and it cannot previously be established that it will be positive)
  long int adj_value = compileTimeSig[&BB] + sumIntraInstruction[&BB] 
    - random_ret_value;

  // 19:   Insert signature update before return instr.
  // 20:     signature ← signature + adjustValue // wrong must be subtracted
  // 21:     if signature != returnVal error()
  Value *Sig = B.CreateLoad(IntType, RuntimeSigGV, true, "checking_sign");
  Value *CmpVal = B.CreateSub(Sig, llvm::ConstantInt::get(IntType, adj_value), "checking_value");
  Value *CmpSig = B.CreateCmp(llvm::CmpInst::ICMP_EQ, CmpVal, 
			      llvm::ConstantInt::get(IntType, random_ret_value));

  if( !Fn.getName().contains("main") ) B.CreateStore(BckupRunSig, RuntimeSigGV);
  B.CreateCondBr(CmpSig, &BB, &ErrBB);
}

PreservedAnalyses RACFED::run(Module &Md, ModuleAnalysisManager &AM) {
  // mappa: istruzione originale -> random r usato per S = S + r
  // std::unordered_map<llvm::Instruction*, int> InstrUpdates;

  auto *I64 = llvm::Type::getInt64Ty(Md.getContext());

  GlobalVariable *RuntimeSig = new GlobalVariable(
    Md, I64,
    /*isConstant=*/false,
    GlobalValue::ExternalLinkage,
    ConstantInt::get(I64, 0),
    "signature"
  );


  createFtFuncs(Md);
  getFuncAnnotations(Md, FuncAnnotations);
  LinkageMap linkageMap = mapFunctionLinkageNames((Md));

  for (Function &Fn : Md) {
    if (shouldCompile(Fn, FuncAnnotations))
      initializeBlocksSignatures(Md, Fn);
  }

  for (Function &Fn: Md) {
    if (Fn.isDeclaration() || Fn.empty()) continue;
    updateCompileSigRandom(Md, Fn, RuntimeSig, I64);
  }

  for(Function &Fn: Md) {
    if(!shouldCompile(Fn, FuncAnnotations)) continue;

    #if GAMBA_DEBUG || MARTI_DEBUG
    errs() << "Analysing func " << Fn.getName() << "\n";
    #endif

    // Search debug location point
    DebugLoc debugLoc;
    for (auto &I : Fn.front()) {
      if (I.getDebugLoc()) {
     	debugLoc = I.getDebugLoc();
      	break;
      } 
    }
 
    // Create error basic block
    assert(!getLinkageName(linkageMap,"SigMismatch_Handler").empty() 
	   && "Function SigMismatch_Handler is missing!");

    BasicBlock *ErrBB = BasicBlock::Create(Fn.getContext(), "ErrBB", &Fn);
    auto CalleeF = ErrBB->getModule()->getOrInsertFunction(
      getLinkageName(linkageMap,"SigMismatch_Handler"),
      FunctionType::getVoidTy(Md.getContext())
    );

    IRBuilder<> ErrIR(ErrBB);
    ErrIR.CreateCall(CalleeF)->setDebugLoc(debugLoc);
    ErrIR.CreateUnreachable();

    Value * runtime_sign_bkup = nullptr;
    for (BasicBlock &BB : Fn) {
      // TODO: Should the error basic block that is inserted be checked?
      // Backup of compile time sign when entering a function
      if( BB.isEntryBlock() ) {
	      IRBuilder<> InstrIR(&*BB.getFirstInsertionPt());
	      runtime_sign_bkup =
	        InstrIR.CreateLoad(I64, RuntimeSig, true, "backup_run_sig");
	      InstrIR.CreateStore(llvm::ConstantInt::get(I64, compileTimeSig[&BB]),

	      RuntimeSig);
      }

      // checkCompileTimeSigAtJump(Md, Fn, BB, RuntimeSig, I64, *ErrBB);
      checkReturnValue(Md, Fn, BB, RuntimeSig, I64, *ErrBB, runtime_sign_bkup);
      checkBranches(Md, BB, RuntimeSig, I64, *ErrBB);
    }
  }

  // There is nothing that this pass preserved
  return PreservedAnalyses::none();
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
