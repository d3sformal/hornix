/*
 *  Copyright (c) 2024, Oliver Glitta <glittaoliver@gmail.com>
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#ifndef SMTOUT_HPP
#define SMTOUT_HPP

#include "Helpers.hpp"

#include <iostream>

namespace hornix {
class SMTOutput {
public:
    explicit SMTOutput(IntegerTheory theory = IntegerTheory::Int) : output(std::cout), theory(theory) {}
    explicit SMTOutput(std::ostream & out, IntegerTheory theory = IntegerTheory::Int) : output(out), theory(theory) {}

    void smt_print_implications(std::vector<Implication> const & implications);

private:
    void smt_declare_functions(std::vector<Implication> const & implications);

    void smt_declare_function(MyConstraint const & predicate);

    void smt_print_constraints(Implication::Constraints const & constraints);

    void smt_declare_implication(Implication const & implication);

    void smt_declare_implications(std::vector<Implication> const & implications) {
        for (auto const & implication : implications) {
            smt_declare_implication(implication);
        }
    }

    std::string toSMTLibType(MyType const & type);

    int smt_quantifiers(Implication const & implication, int indent);

    void print_header() const;
    void print_footer() const;

    std::ostream & output;
    IntegerTheory theory;
    std::unordered_set<std::string> declared_functions;
};
} // namespace hornix

#endif //SMTOUT_HPP
