/*
 *  Copyright (c) 2026, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "SplitErrorCallsPass.hpp"

#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

namespace hornix {
using namespace llvm;

PreservedAnalyses SplitErrorCallsPass::run(Function &F, FunctionAnalysisManager &) {
    SmallVector<Instruction *, 16> split_points;

    for (BasicBlock &block : F) {
        for (Instruction &instruction : block) {
            auto *call = dyn_cast<CallInst>(&instruction);
            if (!call) { continue; }

            Function const *callee = call->getCalledFunction();
            // This matches the backend's error propagation: declarations are
            // modelled as nondeterministic and cannot introduce Hornix's error
            // flag, whereas any defined direct callee may reach reach_error.
            if (!callee || callee->isDeclaration()) { continue; }

            Instruction *next = call->getNextNode();
            // A terminator is translated only on the outgoing edge, so it
            // cannot constrain the error edge of this block.
            if (next && !next->isTerminator()) { split_points.push_back(next); }
        }
    }

    for (Instruction *split_point : split_points) {
        SplitBlock(split_point->getParent(), split_point);
    }

    return split_points.empty() ? PreservedAnalyses::all() : PreservedAnalyses::none();
}

} // namespace hornix
