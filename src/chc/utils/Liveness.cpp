/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "Liveness.hpp"

#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"

namespace hornix {

using namespace llvm;

namespace {
auto compute_usedef(BasicBlock const & BB) {
    ValueSet def;
    ValueSet use;
    for (Instruction const & I : BB) {
        // We do not consider PHI arguments as used in this block, they are specific to the corresponding transition
        if (I.getOpcode() != Instruction::PHI) {
            for (Value * Op : I.operands()) {
                if (isa<Instruction>(Op) or isa<Argument>(Op)) {
                    if (!def.count(Op)) {
                        use.insert(Op);
                    }
                }
            }
        }
        if (I.getType()->isVoidTy()) { continue; }
        def.insert(&I);
    }
    return std::make_pair(use, def);
}

using PhiInfo = std::map<BasicBlock const *, std::vector<Value const *>>;
PhiInfo compute_phi_info(Function const & F) {
    PhiInfo phi_info;
    for (BasicBlock const & BB : F) {
        phi_info[&BB];
        for (Instruction const & I : BB) {
            if (I.getOpcode() != Instruction::PHI) { break; }
            auto const * phi_inst = dyn_cast<PHINode>(&I);
            for (auto const & value : phi_inst->incoming_values()) {
                if (isa<Instruction>(value)) {
                    auto const * incoming_block = phi_inst->getIncomingBlock(value);
                    phi_info[incoming_block].push_back(value);
                }
            }
        }
    }
    return phi_info;
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
    // Step 2: Remember outgoing values to phi instructions
    auto phiInfo = compute_phi_info(F);

    BlockLiveness IN, OUT;

    bool changed = true;
    while (changed) {
        changed = false;

        for (BasicBlock const & BB : llvm::reverse(F)) {
            ValueSet newOut;
            for (auto const & entry : phiInfo.at(&BB)) {
                newOut.insert(entry);
            }
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