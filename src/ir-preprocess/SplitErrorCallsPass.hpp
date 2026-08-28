/*
 *  Copyright (c) 2026, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#ifndef SPLITERRORCALLSPASS_HPP
#define SPLITERRORCALLSPASS_HPP

#include "llvm/IR/PassManager.h"

namespace hornix {

// The CHC backend represents an error raised by a callee as an additional
// output of the call.  Each such call therefore needs to end its basic block:
// constraints from instructions afterwards apply only to the normal return,
// never to the error path.
class SplitErrorCallsPass : public llvm::PassInfoMixin<SplitErrorCallsPass> {
public:
    llvm::PreservedAnalyses run(llvm::Function &F, llvm::FunctionAnalysisManager &);
};

} // namespace hornix

#endif // SPLITERRORCALLSPASS_HPP
