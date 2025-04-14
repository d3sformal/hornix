/*
 *  Copyright (c) 2024, Oliver Glitta <glittaoliver@gmail.com>
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#ifndef CHCTRANSFORM_HPP
#define CHCTRANSFORM_HPP

#include "Helpers.hpp"

namespace hornix {
using Implications = std::vector<Implication>;

class ChcTransform {
public:
  Implications run(llvm::Module &);
};

Implications toChc(llvm::Module &);
} // namespace hornix


#endif //CHCTRANSFORM_HPP
