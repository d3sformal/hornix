/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#ifndef PREPROCESSING_HPP
#define PREPROCESSING_HPP

#include "llvm/IR/Module.h"

namespace hornix {

std::unique_ptr<llvm::Module> transform(std::unique_ptr<llvm::Module> in);

} // hornix


#endif //PREPROCESSING_HPP
