/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#ifndef LIVENESS_HPP
#define LIVENESS_HPP

#include "llvm/IR/Function.h"

#include <map>
#include <unordered_set>

namespace hornix {

class ValueSet {
public:
    using ValuePtr = llvm::Value const *;

    bool contains(ValuePtr v) const;
    void insert(ValuePtr v);
    void insert(ValueSet const & other);
    bool operator!=(ValueSet const & other) const;

    auto begin() const { return values.begin(); }
    auto end() const { return values.end(); }
private:
    std::vector<ValuePtr> values;
    std::unordered_set<ValuePtr> valueSet;
};
using BlockLiveness = std::map<llvm::BasicBlock const *, ValueSet>;

struct LivenessInfo {
    BlockLiveness live_in;
    BlockLiveness live_out;
};

LivenessInfo compute_liveness(llvm::Function const & F);

} // namespace hornix

#endif //LIVENESS_HPP
