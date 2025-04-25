/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "Liveness.hpp"

#include "llvm/IR/CFG.h"

namespace hornix {

using namespace llvm;

namespace {
auto compute_usedef(BasicBlock const & BB) {
    ValueSet def;
    ValueSet use;
    for (Instruction const & I : BB) {
        for (Value * Op : I.operands()) {
            if (isa<Instruction>(Op) or isa<Argument>(Op)) {
                if (!def.count(Op)) {
                    use.insert(Op);
                }
            }
        }
        if (I.getType()->isVoidTy()) { continue; }
        def.insert(&I);
    }
    return std::make_pair(use, def);
}
} // namespace

LivenessInfo compute_liveness(Function const & F) {
    std::map<BasicBlock const *, ValueSet> USE, DEF;

    // Step 1: Compute USE and DEF sets
    for (BasicBlock const & BB : F) {
        auto [use, def] = compute_usedef(BB);
        USE[&BB] = std::move(use);
        DEF[&BB] = std::move(def);
    }

    BlockLiveness IN, OUT;

    bool changed = true;
    while (changed) {
        changed = false;

        for (BasicBlock const & BB : llvm::reverse(F)) {
            ValueSet newOut;
            for (BasicBlock const * Succ : llvm::successors(&BB)) {
                ValueSet & inSucc = IN[Succ];
                newOut.insert(inSucc.begin(), inSucc.end());
            }

            ValueSet newIn = USE[&BB];
            for (Value const * v : newOut) {
                if (not DEF[&BB].count(v)) {
                    newIn.insert(v);
                }
            }

            // Check for changes
            if (newIn != IN[&BB] or newOut != OUT[&BB]) {
                IN[&BB] = std::move(newIn);
                OUT[&BB] = std::move(newOut);
                changed = true;
            }
        }
    }

    return { IN, OUT };
}
} // namespace hornix