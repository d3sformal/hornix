/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "BoolSimplifyPass.hpp"

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PatternMatch.h"

namespace hornix {
using namespace llvm;
using namespace llvm::PatternMatch;
PreservedAnalyses BoolSimplifyPass::run(Function & F, FunctionAnalysisManager &) {
    bool Changed = false;

    SmallVector<Instruction *, 16> ToErase;

    for (BasicBlock & BB : F) {
        for (Instruction & I : BB) {
            Value * A = nullptr;
            Value * B = nullptr;
            bool IsOr = false;
            bool IsAnd = false;

            // Match: and i32 (zext i1 A), (zext i1 B)
            if (match(&I, m_And(m_ZExt(m_Value(A)), m_ZExt(m_Value(B))))) {
                IsAnd = true;
            }
            // Match: or i32 (zext i1 A), (zext i1 B)
            else if (match(&I, m_Or(m_ZExt(m_Value(A)), m_ZExt(m_Value(B))))) {
                IsOr = true;
            }
            if (IsAnd or IsOr && (A->getType()->isIntegerTy(1) && B->getType()->isIntegerTy(1))) {
                IRBuilder<> Builder(&I);
                Value * BoolOp = IsAnd ? Builder.CreateAnd(A, B) : Builder.CreateOr(A, B);

                // Replace uses of the old i32 result
                for (User * U : I.users()) {
                    Instruction * UI = cast<Instruction>(U);
                    IRBuilder<> B2(UI);

                    if (auto * IC = dyn_cast<ICmpInst>(UI)) {
                        // Identify the constant operand
                        Value * Other = (IC->getOperand(0) == &I) ? IC->getOperand(1) : IC->getOperand(0);
                        if (auto const * C = dyn_cast<ConstantInt>(Other)) {
                            // Only valid if constant was 0 or 1 in i32
                            if (C->getZExtValue() == 0 || C->getZExtValue() == 1) {
                                Value * BoolConst = B2.getInt1(C->getZExtValue() == 1);
                                Value * LHS = (&I == IC->getOperand(0)) ? BoolOp : BoolConst;
                                Value * RHS = (&I == IC->getOperand(0)) ? BoolConst : BoolOp;

                                // Rebuild the compare in i1
                                auto * NewIC = B2.CreateICmp(IC->getPredicate(), LHS, RHS);
                                IC->replaceAllUsesWith(NewIC);
                                ToErase.push_back(IC);
                                continue;
                            }
                        }
                    }
                    // Otherwise recreate zext
                    Value * Z = B2.CreateZExt(BoolOp, I.getType());
                    UI->replaceUsesOfWith(&I, Z);
                }
                ToErase.push_back(&I);
                Changed = true;
            }
        }
    }

    for (Instruction * I : ToErase)
        I->eraseFromParent();

    return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}
} // namespace hornix