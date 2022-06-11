#include <unordered_map> 
#include <vector>
#include <algorithm>
#include <string>

#include "llvm/Pass.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/User.h"
#include "llvm/PassAnalysisSupport.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"
#include "RangeAnalysis.h"

using namespace llvm;

// STATISTIC(InstructionsEliminated, "Number of instructions eliminated");
// STATISTIC(BasicBlocksEliminated,  "Number of basic blocks entirely eliminated");

namespace {
class RADeadCodeElimination : public llvm::FunctionPass {
private:
  std::vector<std::pair<BranchInst*, int>> toOverride;

  void replaceConditionalBranch(BranchInst *br, int successorIndex){
    BranchInst* New = BranchInst::Create(br->getSuccessor(successorIndex));
    ICmpInst *cond = dyn_cast<ICmpInst>(br->getCondition());
    ReplaceInstWithInst(br, New);
    RecursivelyDeleteTriviallyDeadInstructions(cond);
  }

  bool solveBranchInstruction(BranchInst* br) {
    if (br->isUnconditional()) return false;
    ICmpInst *I = dyn_cast<ICmpInst>(br->getCondition());
    if(!I) return false;
    InterProceduralRA < Cousot > &ra = getAnalysis < InterProceduralRA < Cousot > >();
    Range range1 = ra.getRange(I->getOperand(0));
    Range range2 = ra.getRange(I->getOperand(1));
    // range1.print(errs());
    // range2.print(errs());
    // I->dump();
    // errs() << '\n';
    
    bool has_changed = false;
    switch (I->getPredicate()) {
      case CmpInst::ICMP_EQ:
        if (range1.getLower() == range1.getUpper() == 
            range2.getLower() == range2.getUpper()) {
          replaceConditionalBranch(br, 0);
          has_changed = true;
        } else {
            if(I->isSigned()) {
              (range1.getUpper().sle(range2.getLower()));
              replaceConditionalBranch(br, 1);
              has_changed = true;
            } else {
              (range2.getUpper().sle(range1.getLower()));
              replaceConditionalBranch(br, 1);
              has_changed = true;
            }
        }
        break;

      case CmpInst::ICMP_UGT:
        if (range1.getLower().ugt(range2.getUpper())) {
          replaceConditionalBranch(br, 0);
          has_changed = true;
        } else if(range1.getUpper().ule(range2.getLower())) {
          replaceConditionalBranch(br, 1);
          has_changed = true;
        }
        break;

      case CmpInst::ICMP_UGE:
        if (range1.getLower().uge(range2.getUpper())) {
          replaceConditionalBranch(br, 0);
          has_changed = true;
        } else if(range1.getUpper().ult(range2.getLower())) {
          replaceConditionalBranch(br, 1);
          has_changed = true;
        }
        break;

      case CmpInst::ICMP_ULT:
        if (range1.getUpper().ult(range2.getLower())) {
          replaceConditionalBranch(br, 0);
          has_changed = true;
        } else if(range1.getLower().uge(range2.getUpper())) {
          replaceConditionalBranch(br, 1);
          has_changed = true;
        }
        break;

      case CmpInst::ICMP_ULE:
        if (range1.getUpper().ule(range2.getLower())) {
          replaceConditionalBranch(br, 0);
          has_changed = true;
        } else if(range1.getLower().ugt(range2.getUpper())) {
          replaceConditionalBranch(br, 1);
          has_changed = true;
        }
        break;

      case CmpInst::ICMP_SGT:
        //This code is always true
        if (range1.getLower().sgt(range2.getUpper())) {
          replaceConditionalBranch(br, 0);
          has_changed = true;
        } else if(range1.getUpper().sle(range2.getLower())) {
          replaceConditionalBranch(br, 1);
          has_changed = true;
        }
        break;

      case CmpInst::ICMP_SGE:
        if (range1.getUpper().sge(range2.getLower())) {
            replaceConditionalBranch(br, 0);
            has_changed = true;
        } else if(range1.getLower().slt(range2.getUpper())) {
          replaceConditionalBranch(br, 1);
          has_changed = true;
        }
        break;

      case CmpInst::ICMP_SLT:
        //This code is always true
        if (range1.getUpper().slt(range2.getLower())) {
          replaceConditionalBranch(br, 0);
          has_changed = true;
        } else if(range1.getLower().sge(range2.getUpper())) {
          replaceConditionalBranch(br, 1);
          has_changed = true;
        }
        break;

        case CmpInst::ICMP_SLE:
        if (range1.getUpper().sle(range2.getLower())) {
          replaceConditionalBranch(br, 0);
          has_changed = true;
        } else if(range1.getLower().sgt(range2.getUpper())) {
          replaceConditionalBranch(br, 1);
          has_changed = true;
        }
        break;

      default: break;
    }
    return has_changed;
  }


public:
  static char ID;
  RADeadCodeElimination() : FunctionPass(ID) {
    this->toOverride = {};
  }
  virtual ~RADeadCodeElimination() {}
  

  virtual bool runOnFunction(Function &F) {
    // InterProceduralRA<Cousot> &ra = getAnalysis<InterProceduralRA<Cousot>>();
    bool has_changed = false;
    for (Function::iterator bb = F.begin(), bbEnd = F.end(); bb != bbEnd; ++bb) {
      if (BranchInst *br = dyn_cast<BranchInst>(--(bb->end()))){
        has_changed |= solveBranchInstruction(br);
      }
    }
    removeUnreachableBlocks(F);
    return has_changed;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<InterProceduralRA<Cousot> >();
  }
};
}

char RADeadCodeElimination::ID = 0;
static RegisterPass<RADeadCodeElimination> X("ra-dead-code-elimination",
                                "Dead code elimination that uses RangeAnalysis");
