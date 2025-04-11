/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#ifndef PREPROCESING_HPP
#define PREPROCESING_HPP

#include "llvm/IR/Module.h"

std::unique_ptr<llvm::Module> transform(std::unique_ptr<llvm::Module> in);



#endif //PREPROCESING_HPP
