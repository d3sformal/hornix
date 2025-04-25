/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#ifndef LIVENESS_HPP
#define LIVENESS_HPP

#include "llvm/IR/Function.h"

#include <map>
#include <set>

namespace hornix {

using ValueSet = std::set<llvm::Value const *>;
using BlockLiveness = std::map<llvm::BasicBlock const *, ValueSet>;

struct LivenessInfo {
    BlockLiveness live_in;
    BlockLiveness live_out;
};

LivenessInfo compute_liveness(llvm::Function const & F);

} // namespace hornix

#endif //LIVENESS_HPP
