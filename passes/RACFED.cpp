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
std::mt19937 rng64(0x5EED00); // constant seed for reproducibility

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

void RACFED::initializeBlocksSignatures(Function &Fn) {
  std::mt19937 rng(0xB00BA5); // constant seed for reproducibility
  uint32_t randomBB;
  uint32_t randomSub;

  for (BasicBlock &BB : Fn) {
    do {
      randomBB = dist32(rng);
    } while ( isNotUniqueCompileTimeSig(randomBB, compileTimeSig) );

    do {
      randomSub = dist32(rng);
    } while ( isNotUnique(
      randomBB + randomSub,
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

void RACFED::updateCompileSigRandom(Function &Fn,
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

      Value *Sig = B.CreateLoad(IntType, RuntimeSigGV);
      Value *NewSig = B.CreateAdd(Sig, ConstantInt::get(IntType, K), "sig_add");
      B.CreateStore(NewSig, RuntimeSigGV);
      sumIntraInstruction[&BB] = partial_sum;
    }
  }
}

// --- CHECK BLOCKS AT JUMP END ---
// FIXME: Fix warnings
void RACFED::checkJumpSignature(BasicBlock &BB,
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

    // Fix PHI nodes in successors
    // replaceAllUsesWith updates PHI nodes in successors to point to NewBB,
    // but the actual control flow is NewBB -> BB -> Succ, so Succ still sees BB
    // as predecessor.
    for (BasicBlock *Succ : successors(&BB)) {
      for (PHINode &Phi : Succ->phis()) {
        for (unsigned i = 0; i < Phi.getNumIncomingValues(); ++i) {
          if (Phi.getIncomingBlock(i) == NewBB) {
            Phi.setIncomingBlock(i, &BB);
          }
        }
      }
    }

    // add instructions for checking the runtime signature
    Value *CmpVal =
    BChecker.CreateCmp(llvm::CmpInst::ICMP_EQ, RuntimeSignatureVal,
		       llvm::ConstantInt::get(IntType, randomNumberBB));
    BChecker.CreateCondBr(CmpVal, &BB, &ErrBB);

    // add NewBB and BB into the NewBBs map
    NewBBs.insert(std::pair<BasicBlock *, BasicBlock *>(NewBB, &BB));

    // Map NewBB to the same signature requirements as BB so predecessors can
    // target it correctly
    compileTimeSig[NewBB] = randomNumberBB;
    subRanPrevVals[NewBB] = subRanPrevVal;
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

Value *RACFED::getCondition(Instruction &I) {
  if (isa<BranchInst>(I) && cast<BranchInst>(I).isConditional()) {
    if (!cast<BranchInst>(I).isConditional()) {
      return nullptr;
    } else {
      return cast<BranchInst>(I).getCondition();
    }
  } else if (isa<SwitchInst>(I)) {
    errs() << "There is a switch!\n";
    abort();
    return cast<SwitchInst>(I).getCondition();
  } else {
    assert(false && "Tried to get a condition on a function that is not a "
                    "branch or a switch");
  }
}

static void printSig(Module &Md, IRBuilder<> &B, Value *SigVal, const char *Msg) {
  LLVMContext &Ctx = Md.getContext();

  // int printf(const char*, ...)
  FunctionCallee Printf = Md.getOrInsertFunction(
      "printf",
      FunctionType::get(IntegerType::getInt32Ty(Ctx),
                        PointerType::getUnqual(Ctx),
                        true));

  // Crea stringa globale "Msg: %ld\n"
  std::string Fmt = std::string(Msg) + ": %ld\n";
  Value *FmtStr = B.CreateGlobalStringPtr(Fmt);


  if (SigVal->getType()->isIntegerTy(32)) {
    SigVal = B.CreateZExt(SigVal, Type::getInt64Ty(Ctx));
  }

  B.CreateCall(Printf, {FmtStr, SigVal});
}

/*
* checkBranches
23:   for all Successor of BB do
24:    adjustValue ← (compileTimeSigBB + \Sum{instrMonUpdates}) -
25:     (compileTimeSigsuccs + subRanPrevValsuccs)
26:   Insert signature update at BB end
27:     signature ← signature + adjustValue
*/
void RACFED::checkBranches(Module &Md, BasicBlock &BB,  GlobalVariable *RuntimeSigGV,
			   Type *IntType) {
  Instruction *Term = BB.getTerminator();
  IRBuilder<> B(&BB);
  B.SetInsertPoint(Term);
  auto *BI = dyn_cast<BranchInst>(Term);
  if (!BI) return;

  //TODO: check this

  // Calculate Source Static Signature: CT_BB + SumIntra
  uint64_t SourceStatic =
      static_cast<uint64_t>(compileTimeSig[&BB]) + sumIntraInstruction[&BB];

  Value *Current = B.CreateLoad(IntType, RuntimeSigGV, "current");
  printSig(Md, B, Current, "current");

  //TODO: until here

  //define if conditional or unconditional branch
  //Conditional: expected= CT_succ+subRan_succ
  //adj = CTB-exp--> new signature = RT -adj
  if ( BI->isUnconditional() ) {  // only one successor
      BasicBlock *Succ = BI->getSuccessor(0);
      uint64_t Expected =
            static_cast<uint64_t>(compileTimeSig[Succ] + subRanPrevVals[Succ]);
      // adj = expected - current
      uint64_t AdjValue = Expected - SourceStatic;
      Value *Adj = ConstantInt::get(IntType, AdjValue);
      Value *NewSig = B.CreateAdd(Current, Adj, "racfed_newsig");
      B.CreateStore(NewSig, RuntimeSigGV);
      printSig(Md,B, NewSig, "newsig");

      return;
  }

  if ( BI-> isConditional()) {
    BasicBlock *SuccT = BI->getSuccessor(0);
    BasicBlock *SuccF = BI->getSuccessor(1);
    Instruction *Terminator = BB.getTerminator();
    Value *BrCondition = getCondition(*Terminator);

    // Target T
    uint64_t expectedT =
        static_cast<uint64_t>(compileTimeSig[SuccT] + subRanPrevVals[SuccT]);
    uint64_t adj1 = expectedT - SourceStatic;

    // Target F
    uint64_t expectedF =
        static_cast<uint64_t>(compileTimeSig[SuccF] + subRanPrevVals[SuccF]);
    uint64_t adj2 = expectedF - SourceStatic;

    Value *Adj = B.CreateSelect(BrCondition, ConstantInt::get(IntType, adj1), ConstantInt::get(IntType, adj2));
    Value *NewSig = B.CreateAdd(Current, Adj, "racfed_newsig");
    B.CreateStore(NewSig, RuntimeSigGV);

    printSig(Md, B, NewSig, "SIG after cond");
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
Instruction *RACFED::checkReturnValue(BasicBlock &BB,
			      GlobalVariable *RuntimeSigGV, 
			      Type* IntType, BasicBlock &ErrBB,
			      Value *BckupRunSig) {
  Instruction *Term = BB.getTerminator();

  if( !isa<ReturnInst>(Term) ) return nullptr;

  std::vector<Instruction*> org_instr;
  originalInstruction(BB, org_instr);
  if( org_instr.size() > 2 ) {

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
      BB.getContext(), 
      "RAFCED_ret_verification_BB", 
      BB.getParent(),
      &BB
    );

    // Relinking the basic blocks so that the structure 
    // results in: BeforeRetBB->ControlBB->BB
    BeforeRetBB->getTerminator()->replaceSuccessorWith(&BB, ControlBB);

    // Inserting instructions into ControlBB
    IRBuilder<> ControlIR(ControlBB);
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
    Value *Sig = ControlIR.CreateLoad(IntType, RuntimeSigGV, true, "checking_sign");
    Value *CmpVal = ControlIR.CreateSub(Sig, llvm::ConstantInt::get(IntType, adj_value), "checking_value");
    Value *CmpSig = ControlIR.CreateCmp(llvm::CmpInst::ICMP_EQ, CmpVal, 
				llvm::ConstantInt::get(IntType, random_ret_value));

    ControlIR.CreateCondBr(CmpSig, &BB, &ErrBB);
  }

  return Term;
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
  Instruction *RetInst = nullptr;

  createFtFuncs(Md);
  getFuncAnnotations(Md, FuncAnnotations);
  LinkageMap linkageMap = mapFunctionLinkageNames((Md));

  for (Function &Fn : Md) {
    if (shouldCompile(Fn, FuncAnnotations))
      initializeBlocksSignatures(Fn);
  }

  for (Function &Fn: Md) {
    if (Fn.isDeclaration() || Fn.empty()) continue;
    updateCompileSigRandom(Fn, RuntimeSig, I64);
  }

  for(Function &Fn: Md) {
    if(!shouldCompile(Fn, FuncAnnotations)) continue;

    #if MARTI_DEBUG
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

      checkJumpSignature(BB, RuntimeSig, I64, *ErrBB);
      RetInst = checkReturnValue(BB, RuntimeSig, I64, *ErrBB, runtime_sign_bkup);
      checkBranches(Md, BB, RuntimeSig, I64);

      // Restore signature on return
      if( RetInst != nullptr ) {
	      IRBuilder<> RetInstIR(RetInst);
	      RetInstIR.CreateStore(runtime_sign_bkup, RuntimeSig);
      }
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

