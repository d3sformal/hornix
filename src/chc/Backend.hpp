/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#ifndef BACKEND_HPP
#define BACKEND_HPP

#include <optional>
#include <string>

namespace hornix {
struct SolverContext {
  std::string solver;
  std::optional<std::string> solver_dir;
  std::string args;

  static SolverContext z3_default();
};

using Result = std::string;

Result solve(std::string query);
Result solve(std::string query, SolverContext context);
} // namespace hornix


#endif //BACKEND_HPP
