#include "Helpers.hpp"

namespace hornix {
// TODO: Implement this as a visitor
std::set<MyVariable> all_vars(Implication const & implication) {
    std::set<MyVariable> vars;
    auto process = [&](MyVariable const & var) {
        if (not var.isConstant) {
            vars.insert(var);
        }
    };
    for (auto const & var : implication.head.vars) {
        process(var);
    }
    for (auto const & constraint : implication.constraints) {
        if (MyPredicate * pred = dynamic_cast<MyPredicate *>(constraint.get())) {
            for (auto const & var : pred->vars) {
                process(var);
            }
        } else if (auto * equality = dynamic_cast<Equality *>(constraint.get())) {
            process(equality->lhs);
            process(equality->rhs);
        } else if (auto * unary = dynamic_cast<UnaryConstraint *>(constraint.get())) {
            process(unary->result);
            process(unary->value);
        } else if (auto * binary = dynamic_cast<BinaryConstraint *>(constraint.get())) {
            process(binary->result);
            process(binary->operand1);
            process(binary->operand2);
        } else if (auto * cmp = dynamic_cast<ComparisonConstraint *>(constraint.get())) {
            process(cmp->operand1);
            process(cmp->operand2);
        } else if (auto * ite = dynamic_cast<ITEConstraint *>(constraint.get())) {
            process(ite->result);
            process(ite->condition);
            process(ite->operand1);
            process(ite->operand2);
        } else {
            throw std::logic_error("Unhandled constraint type!");
        }

    }
    return vars;
}
} // namespace hornix


