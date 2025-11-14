/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#ifndef BOOLSIMPLIFYPASS_HPP
#define BOOLSIMPLIFYPASS_HPP

#include "llvm/IR/PassManager.h"

namespace hornix {

class BoolSimplifyPass : public llvm::PassInfoMixin<BoolSimplifyPass> {
public:
    llvm::PreservedAnalyses run(llvm::Function &F, llvm::FunctionAnalysisManager &);
};

} // namespace hornix



#endif //BOOLSIMPLIFYPASS_HPP
