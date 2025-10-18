#include "Helpers.hpp"

namespace hornix {
// TODO: Implement this as a visitor

using vars_t = std::set<MyVariable>;
void collect_vars(MyConstraint const * constraint, vars_t & vars) {
    auto process = [&](MyVariable const & var) {
        if (not var.isConstant) {
            vars.insert(var);
        }
    };
    if (MyPredicate const * pred = dynamic_cast<MyPredicate const *>(constraint)) {
        for (auto const & var : pred->vars) {
            process(var);
        }
    } else if (auto * equality = dynamic_cast<Equality const *>(constraint)) {
        process(equality->lhs);
        process(equality->rhs);
    } else if (auto * unary = dynamic_cast<UnaryConstraint const *>(constraint)) {
        process(unary->result);
        process(unary->value);
    } else if (auto * binary = dynamic_cast<BinaryConstraint const *>(constraint)) {
        process(binary->result);
        process(binary->operand1);
        process(binary->operand2);
    } else if (auto * cmp = dynamic_cast<ComparisonConstraint const *>(constraint)) {
        process(cmp->operand1);
        process(cmp->operand2);
    } else if (auto * ite = dynamic_cast<ITEConstraint const *>(constraint)) {
        process(ite->result);
        process(ite->condition);
        process(ite->operand1);
        process(ite->operand2);
    } else if (auto * neg = dynamic_cast<Not const *>(constraint)) {
        collect_vars(neg->inner.get(), vars);
    } else if (auto * conj = dynamic_cast<And const *>(constraint)) {
        for (auto const & arg : conj->args) {
            collect_vars(arg.get(), vars);
        }
    } else {
        throw std::logic_error("Unhandled constraint type!");
    }
}

std::set<MyVariable> all_vars(Implication const & implication) {
    std::set<MyVariable> vars;
    collect_vars(&implication.head, vars);
    for (auto const & constraint : implication.constraints) {
        collect_vars(constraint.get(), vars);
    }
    return vars;
}

BitvectorType BitvectorType::make(bvsize_t size) {
    return BitvectorType(size);
}

} // namespace hornix


