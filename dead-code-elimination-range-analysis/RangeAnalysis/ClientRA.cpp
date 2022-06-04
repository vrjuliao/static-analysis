#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/User.h"
#include "llvm/PassAnalysisSupport.h"
#include "llvm/Support/raw_ostream.h"
#include "RangeAnalysis.h"

using namespace llvm;

namespace {
class ClientRA : public llvm::FunctionPass {
public:
  static char ID;
  ClientRA() : FunctionPass(ID) {}
  virtual ~ClientRA() {}
  virtual bool runOnFunction(Function &F) {
    InterProceduralRA<Cousot> &ra = getAnalysis<InterProceduralRA<Cousot>>();

    errs() << "\nCousot Intra Procedural analysis (Values -> Ranges) of "
           << F.getName() << ":\n";
    for (Function::iterator bb = F.begin(), bbEnd = F.end(); bb != bbEnd;
         ++bb) {
      errs() << bb->getName().str() << '\n';
      for (BasicBlock::iterator I = bb->begin(), IEnd = bb->end(); I != IEnd;
           ++I) {
        const Value *v = &(*I);
        Range r = ra.getRange(v);
        if (!r.isUnknown()) {
          r.print(errs());
          I->dump();
        }
      }
    }
    return false;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<InterProceduralRA<Cousot> >();
  }
};
}

char ClientRA::ID = 0;
static RegisterPass<ClientRA> X("client-ra",
                                "A client that uses RangeAnalysis");
