/*
 *  Copyright (c) 2024, Oliver Glitta <glittaoliver@gmail.com>
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "ChcTransform.hpp"
#include "utils/Liveness.hpp"

#include <Exceptions.hpp>

#include <llvm/IR/Constants.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Value.h>

using namespace llvm;

namespace hornix {
class Context {
public:
    static Context create(Module const & module);

    void analyze(Function const & F /*, FunctionAnalysisManager & AM*/);

    Implications finish();

    using GlobalInfo = llvm::DenseMap<GlobalVariable const *, std::pair<std::string, int>>;

private:
    void add_global_variables(std::vector<MyVariable> & vars, MyFunctionInfo const & function_info);

    Implication::Constraints transform_function_call(Instruction const * I, MyFunctionInfo & function_info);

    std::vector<Implication> transform_basic_blocks(MyFunctionInfo & function_info);

    Implication::Constraints transform_instructions(MyBasicBlock const & BB, MyFunctionInfo & function_info);

    std::unique_ptr<Equality> transform_load_operand(Instruction const * I);

    std::unique_ptr<Equality> transform_store_operand(Instruction const * I);

    std::vector<std::unique_ptr<UnaryConstraint>> transform_phi_instructions(MyBasicBlock const & predecessor,
                                                                             MyBasicBlock const & successor);

    Implication get_entry_block_implication(MyFunctionInfo const & function_info, MyBasicBlock const & BB1);

    MyPredicate create_basic_block_predicate(MyBasicBlock const & BB, BasicBlockPredicateType type,
                                             MyFunctionInfo const & function_info);

    Implication create_entry_to_exit(MyBasicBlock const & BB, MyFunctionInfo & function_info);

    MyPredicate get_function_predicate(MyFunctionInfo const & function_info, MyVariable e_in, MyVariable e_out);

    MyPredicate get_fail_block_predicate(MyFunctionInfo const & function_info);

    GlobalInfo global_vars;
    Implications implications;
};

namespace {
Context::GlobalInfo get_global_info(Module const & module) {
    Context::GlobalInfo global_info;
    auto globals = module.globals();
    unsigned j = 0u;
    for (GlobalVariable const & var : globals) {
        if (var.getValueType()->isIntegerTy()) {
            auto name = "g" + std::to_string(j);
            auto value = std::make_pair(std::move(name), 0);
            global_info.insert(std::make_pair(&var, std::move(value)));
            j++;
        }
    }
    return global_info;
}
} // namespace

Context Context::create(Module const & module) {
    Context context;
    context.global_vars = get_global_info(module);
    return context;
}

Implications Context::finish() {
    return std::move(implications);
}

namespace {
MyFunctionInfo load_basic_info(Function const & F) {
    auto function_name = F.getName().str();
    bool is_main_function = isMainFunction(function_name);
    MyFunctionInfo function_info(F, function_name, is_main_function);

    return function_info;
}

MyFunctionInfo::BasicBlocks load_basic_blocks(Function const & F) {
    MyFunctionInfo::BasicBlocks basic_blocks;
    unsigned bb_index = 1;
    std::string const function_name = F.getName().str();

    for (BasicBlock const & BB : F) {
        auto name = function_name + std::to_string(bb_index);
        MyBasicBlock myBB(&BB, std::move(name), bb_index);
        basic_blocks.insert(std::make_pair(bb_index, myBB));
        ++bb_index;
    }

    return basic_blocks;
}

// Get type of variable
BitvectorType get_type(Type const * type) {
    if (type->isIntegerTy()) {
        auto w = cast<IntegerType>(type)->getBitWidth();
        return BitvectorType::make(w);
    }
    throw UnsupportedFeature("Unknown type of variable.");
}

std::string convert_name_to_string(Value const * const value) {
    std::string name;
    raw_string_ostream string_stream(name);
    value->printAsOperand(string_stream, false);
    return name;
}

MyVariable convert_name_to_myvar(Value const * const value) {
    return MyVariable::variable(convert_name_to_string(value), get_type(value->getType()));
}

MyVariable convert_operand_to_myvar(Value const * value) {
    if (auto const * asConstant = dyn_cast<ConstantInt>(value)) {
        auto type = get_type(value->getType());
        auto const num = asConstant->getSExtValue();
        if (type.size() != 1) {
            // FIXME: Store value directly, not string representation
            auto name = num < 0 ? "(- " + std::to_string(num * -1) + ')' : std::to_string(num);
            return MyVariable::constant(std::move(name));
        }
        assert(type.size() == 1);
        return MyVariable::constant(num != 0 ? "true" : "false");
    }
    return convert_name_to_myvar(value);
}

std::optional<std::int8_t> get_block_id_by_link(BasicBlock const * block,
                                                MyFunctionInfo::BasicBlocks const & my_blocks) {
    for (auto const & [id, my_block] : my_blocks) {
        if (my_block.BB_link == block) { return id; }
    }
    return std::nullopt;
}

void set_basic_block_info(MyFunctionInfo * function_info) {
    for (auto & it : function_info->basic_blocks) {
        MyBasicBlock & BB = it.second;
        BasicBlock const * block_link = BB.BB_link;

        // Set Predecessors of blocks and variables from them
        for (auto pred : predecessors(block_link)) {
            auto maybe_pred_id = get_block_id_by_link(pred, function_info->basic_blocks);
            if (maybe_pred_id.has_value()) {
                auto pred_id = maybe_pred_id.value();
                // Add predecessor
                BB.predecessors.push_back(pred_id);
            }
        }

        // Set successors of block
        for (auto succ : successors(block_link)) {
            auto maybe_succ_id = get_block_id_by_link(succ, function_info->basic_blocks);
            assert(maybe_succ_id.has_value());
            BB.successors.push_back(maybe_succ_id.value());
        }

        // Find all used variables in instructions
        for (Instruction const & I : block_link->instructionsWithoutDebug()) {

            // See if basic block handles failed assertion
            if (isFailedAssertCall(I)) {
                BB.isFalseBlock = true;
                break;
            }

            // Remember function called in basic block (no assert)
            if (I.getOpcode() == Instruction::Call) {
                if (Function const * fn = dyn_cast<CallInst>(&I)->getCalledFunction(); fn and not fn->isDeclaration()) {
                    BB.isFunctionCalled = true;
                }
            }

            // Remember return value of function
            if (I.getOpcode() == Instruction::Ret) {
                if (not function_info->llvm_function.getReturnType()->isVoidTy()) {
                    auto o = I.getOperand(0);
                    function_info->return_value = convert_operand_to_myvar(o);
                }
                BB.isLastBlock = true;
            }
        }
    }
}

MyFunctionInfo load_my_function_info(Function const & F) {
    MyFunctionInfo function_info = load_basic_info(F);
    function_info.basic_blocks = load_basic_blocks(F);
    set_basic_block_info(&function_info);
    function_info.liveness_info = compute_liveness(F);
    return function_info;
}

// Create constraint for br instruction
std::unique_ptr<MyConstraint> get_transition_constraint(Instruction const * I, BasicBlock const * successor) {
    if (I->getOpcode() == Instruction::Br) {
        if (I->getNumOperands() == 1) { return nullptr; } // Unconditional jump
        if (I->getNumOperands() != 3) { throw std::logic_error("Wrong instruction. Too few function operands."); }
        MyVariable res = MyVariable::constant(successor == I->getOperand(2) ? "true" : "false");
        return std::make_unique<Equality>(convert_operand_to_myvar(I->getOperand(0)), res);
    }
    if (I->getOpcode() == Instruction::Switch) {
        SwitchInst const * switch_inst = dyn_cast<SwitchInst>(I);
        if (switch_inst->getDefaultDest() == successor) {
            // TODO: We could detect if the cases are a continuous range and use simpler condition here
            Implication::Constraints cases_constraints;
            auto condition_var = convert_name_to_myvar(switch_inst->getCondition());
            for (auto const & switch_case : switch_inst->cases()) {
                cases_constraints.push_back(std::make_unique<Not>(std::make_unique<Equality>(
                    condition_var,
                    convert_operand_to_myvar(switch_case.getCaseValue())
                    )));
            }
            return std::make_unique<And>(std::move(cases_constraints));
        }
        for (auto const & switch_case : switch_inst->cases()) {
            if (switch_case.getCaseSuccessor() == successor) {
                return std::make_unique<Equality>(
                    convert_name_to_myvar(switch_inst->getCondition()),
                    convert_operand_to_myvar(switch_case.getCaseValue())
                );
            }
        }
        throw std::logic_error("Error in processing switch");
    }
    throw UnsupportedFeature("Unknown terminator instruction!");
}

MyVariable makeErrorVariable(std::string name) {
    return MyVariable::variable(std::move(name), BitvectorType::make(1));
}

bool isBoolLike(BitvectorType const & bvtype) { return bvtype.size() == 1; }

} // namespace

void Context::analyze(Function const & F) {
    auto function_info = load_my_function_info(F);
    auto implications = transform_basic_blocks(function_info);
    std::move(implications.begin(), implications.end(), std::back_inserter(this->implications));
}

std::vector<Implication> Context::transform_basic_blocks(MyFunctionInfo & function_info) {

    std::vector<Implication> clauses;
    clauses.push_back(get_entry_block_implication(function_info, function_info.basic_blocks.at(1)));

    for (auto const & [id, BB] : function_info.basic_blocks) {
        // Skip failed assert basic blocks
        if (BB.isFalseBlock) { continue; }

        // Create implication of current basic block (entry -> exit)
        clauses.push_back(create_entry_to_exit(BB, function_info));

        // Create implications for transfers to successors
        for (auto & succ : BB.successors) {
            auto current_exit_predicate = create_basic_block_predicate(BB, BasicBlockPredicateType::EXIT, function_info);

            auto const & successor = function_info.basic_blocks.at(succ);
            auto succ_predicate = create_basic_block_predicate(successor, BasicBlockPredicateType::ENTRY, function_info);

            // Create implication
            Implication implication(succ_predicate);

            if (BB.isFunctionCalled) {
                current_exit_predicate.vars.push_back(MyVariable::constant("false"));
            }

            // Add current BB exit predicate
            implication.constraints.push_back(std::make_unique<MyPredicate>(current_exit_predicate));

            // Translate phi instructions
            for (auto && constraint : transform_phi_instructions(BB, successor)) {
                implication.constraints.push_back(std::move(constraint));
            }

            // Transition constraint
            if (BB.successors.size() > 0) {
                if (auto const * terminator = BB.BB_link->getTerminator()) {
                    if (auto transition_constraint = get_transition_constraint(terminator, successor.BB_link)) {
                        implication.constraints.push_back(std::move(transition_constraint));
                    }
                }
            }

            implication.head = succ_predicate;
            clauses.push_back(std::move(implication));
        }

        // Add predicate if error in called function
        if (BB.isFunctionCalled) {
            auto fail = get_fail_block_predicate(function_info);
            Implication implication(fail);

            MyPredicate current_exit_predicate = create_basic_block_predicate(BB, BasicBlockPredicateType::EXIT, function_info);
            current_exit_predicate.vars.push_back(MyVariable::constant("true"));
            implication.constraints.push_back(std::make_unique<MyPredicate>(current_exit_predicate));

            clauses.push_back(std::move(implication));
        }

        // From return instruction to function predicate implication
        if (BB.isLastBlock) {
            auto fun_predicate = get_function_predicate(function_info, MyVariable::constant("false"), MyVariable::constant("false"));

            auto implication = Implication(fun_predicate);

            MyPredicate current_exit_predicate = create_basic_block_predicate(BB, BasicBlockPredicateType::EXIT, function_info);
            if (BB.isFunctionCalled) { current_exit_predicate.vars.push_back(MyVariable::constant("false")); }
            implication.constraints.push_back(std::make_unique<MyPredicate>(current_exit_predicate));

            clauses.push_back(std::move(implication));
        }
    }

    // Add error case implication
    if (function_info.is_main_function) {
        Implication implication = Implication(MyPredicate("false"));
        MyPredicate fail_predicate = get_fail_block_predicate(function_info);
        implication.constraints.push_back(std::make_unique<MyPredicate>(fail_predicate));
        clauses.push_back(std::move(implication));
    } else {
        auto function_predicate = get_function_predicate(function_info, MyVariable::constant("true"), MyVariable::constant("true"));
        clauses.emplace_back(function_predicate);
    }

    return clauses;
}

void Context::add_global_variables(std::vector<MyVariable> & vars, MyFunctionInfo const & function_info) {
    for (auto const & [llvm_global, entry] : global_vars) {
        auto const & [name, index] = entry;
        auto type_name = get_type(llvm_global->getValueType());
        if (not function_info.is_main_function) {
            // Global value at the entry point of the function
            vars.push_back(MyVariable::variable(name, type_name));
        }
        // Current value of the global
        vars.push_back(MyVariable::variable(name + "_" + std::to_string(index), type_name));
    }
}



// Create implication from entry to exit point in basic block
Implication Context::create_entry_to_exit(MyBasicBlock const & BB, MyFunctionInfo & function_info) {

    MyPredicate entry_predicate = create_basic_block_predicate(BB, BasicBlockPredicateType::ENTRY, function_info);

    Implication::Constraints constraints = transform_instructions(BB, function_info);

    auto exit_predicate = create_basic_block_predicate(BB, BasicBlockPredicateType::EXIT, function_info);

    // Add last output error variable if some function called in BB
    if (BB.isFunctionCalled) {
        exit_predicate.vars.push_back(makeErrorVariable("e" + std::to_string(function_info.e_index)));
    }

    constraints.push_back(std::make_unique<MyPredicate>(entry_predicate));
    Implication implication(exit_predicate);
    implication.constraints = std::move(constraints);
    return implication;
}

// Create constraints for function call
Implication::Constraints Context::transform_function_call(Instruction const * I, MyFunctionInfo & function_info) {
    Implication::Constraints result;
    CallInst const * call_inst = cast<CallInst>(I);

    // Get function from instruction
    Function * fn = call_inst->getCalledFunction();
    std::string function_name = fn ? fn->getName().str() : convert_name_to_string(I->getOperand(0));

    // If function not declared, check name for predefined non-deterministic functions
    if (!fn || fn->isDeclaration()) {
        if (function_name.find(UNSIGNED_UINT_FUNCTION, 0) != std::string::npos) {

            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_myvar(I), ">=", MyVariable::constant("0")));
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_myvar(I), "<=", MyVariable::constant("4294967295")));
        } else if (function_name.find(UNSIGNED_SHORT_FUNCTION, 0) != std::string::npos) {
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_myvar(I), ">=", MyVariable::constant("(- 32768)")));
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_myvar(I), "<=", MyVariable::constant("32767")));
        } else if (function_name.find(UNSIGNED_USHORT_FUNCTION, 0) != std::string::npos) {
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_myvar(I), ">=", MyVariable::constant("0")));
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_myvar(I), "<=", MyVariable::constant("65535")));

        } else if (function_name.find(UNSIGNED_UCHAR_FUNCTION, 0) != std::string::npos) {

            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_myvar(I), ">=", MyVariable::constant("0")));
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_myvar(I), "<=", MyVariable::constant("255")));

        } else if (function_name.find(UNSIGNED_CHAR_FUNCTION, 0) != std::string::npos) {

            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_myvar(I), ">=", MyVariable::constant("(- 128)")));
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_myvar(I), "<=", MyVariable::constant("127")));

        } else {
            // If no predefined function, ignore call and add true constraint
            result.push_back(std::make_unique<MyPredicate>("true"));
        }
        return result;
    }

    auto predicate = std::make_unique<MyPredicate>(function_name);

    // Add parameters
    for (auto arg = call_inst->arg_begin(); arg != call_inst->arg_end(); ++arg) {
        predicate->vars.push_back(convert_operand_to_myvar(arg->get()));
    }

    // Add return variable
    if (!fn->getReturnType()->isVoidTy()) {
        predicate->vars.push_back(convert_name_to_myvar(I));
    }

    // Add variables for input error variable
    if (function_info.e_index == 0) {
        predicate->vars.push_back(MyVariable::constant("false"));
    } else {
        predicate->vars.push_back(makeErrorVariable("e" + std::to_string(function_info.e_index)));
    }

    // Add variables for output error variable
    ++function_info.e_index;
    predicate->vars.push_back(makeErrorVariable("e" + std::to_string(function_info.e_index)));

    // Add global variables input and output values
    for (auto & [var, entry] : global_vars) {
        auto & [name, index] = entry;
        auto bvtype = get_type(var->getValueType());
        predicate->vars.push_back(MyVariable::variable(name + "_" + std::to_string(index), bvtype));
        index++;
        predicate->vars.push_back(MyVariable::variable(name + "_" + std::to_string(index), bvtype));
    }

    result.push_back(std::move(predicate));
    return result;
}

namespace {

// Transform Cmp instruction
std::string cmp_sign(Instruction const * I) {
    CmpInst const * CmpI = cast<CmpInst>(I);
    switch (CmpI->getPredicate()) {
        case CmpInst::ICMP_EQ:
            return "=";
        case CmpInst::ICMP_NE:
            return "!=";
        case CmpInst::ICMP_UGT:
        case CmpInst::ICMP_SGT:
            return ">";
        case CmpInst::ICMP_UGE:
        case CmpInst::ICMP_SGE:
            return ">=";
        case CmpInst::ICMP_ULT:
        case CmpInst::ICMP_SLT:
            return "<";
        case CmpInst::ICMP_ULE:
        case CmpInst::ICMP_SLE:
            return "<=";
        default:
            throw UnsupportedFeature("Unknown comparison symbol.");
        break;
    }
}

// Create binary constraint for comparison instruction
std::unique_ptr<BinaryConstraint> transform_comparison(Instruction const * I) {
    CmpInst const * comparison = cast<CmpInst>(I);
    auto sign = cmp_sign(comparison);
    auto * lhs = comparison->getOperand(0);
    auto * rhs = comparison->getOperand(1);

    // Get constant value as signed or unsigned based on type of comparison
    auto as_my_var = [&](Value * val) -> MyVariable {
        if (auto asConstant = dyn_cast<ConstantInt>(val)) {
            if (comparison->isSigned()) {
                auto value = asConstant->getSExtValue();
                // FIXME!
                if (value < 0) { return MyVariable::constant("(- " + std::to_string(value * -1) + ')'); }
                return MyVariable::constant(std::to_string(value));
            } else {
                auto value = asConstant->getZExtValue();
                return MyVariable::constant(std::to_string(value));
            }
        }
        return convert_name_to_myvar(val);
    };

    return std::make_unique<BinaryConstraint>(convert_name_to_myvar(comparison), as_my_var(lhs), sign, as_my_var(rhs));
}

// Create binary constraint from binary instructions
std::unique_ptr<BinaryConstraint> transform_binary_inst(Instruction const * I) {
    std::string sign;
    switch (I->getOpcode()) {
        case Instruction::ICmp:
            return transform_comparison(I);
        case Instruction::Add:
            sign = "+";
        break;
        case Instruction::Sub:
            sign = "-";
        break;
        case Instruction::Mul:
            sign = "*";
        break;
        case Instruction::UDiv:
        case Instruction::SDiv:
            sign = "div";
        break;
        case Instruction::URem:
        case Instruction::SRem:
            sign = "mod";
        break;
        case Instruction::Xor:
            sign = "xor";
        break;
        case Instruction::And:
            sign = "and";
        break;
        case Instruction::Or:
            sign = "or";
        break;
        default:
            throw UnsupportedFeature("Unknown binary instruction.");
    }

    return std::make_unique<BinaryConstraint>(convert_name_to_myvar(I), convert_operand_to_myvar(I->getOperand(0)),
                                              sign, convert_operand_to_myvar(I->getOperand(1)));
}

// Create constraint for zext instruction
std::unique_ptr<MyConstraint> transform_zext(Instruction const * I) {
    MyVariable input = convert_operand_to_myvar(I->getOperand(0));
    MyVariable output = convert_name_to_myvar(I);

    if (isBoolLike(input.type) and not isBoolLike(output.type)) {
        return std::make_unique<ITEConstraint>(output, input, MyVariable::constant("1"), MyVariable::constant("0"));
    } else {
        return std::make_unique<UnaryConstraint>(std::move(output), std::move(input));
    }
}

std::unique_ptr<MyConstraint> transform_select(SelectInst const * I) {
    return std::make_unique<ITEConstraint>(
        convert_name_to_myvar(I),
        convert_operand_to_myvar(I->getCondition()),
        convert_operand_to_myvar(I->getTrueValue()),
        convert_operand_to_myvar(I->getFalseValue())
    );
}

// Create constraint for trunc instruction
std::unique_ptr<MyConstraint> transform_trunc(Instruction const * I) {
    MyVariable input = convert_operand_to_myvar(I->getOperand(0));
    MyVariable output = convert_name_to_myvar(I);

    if (not isBoolLike(input.type) and isBoolLike(output.type)) {
        return std::make_unique<BinaryConstraint>(output, input, "!=", MyVariable::constant("0"));
    } else {
        auto out_size = output.type.size();
        if (output.type.size() < input.type.size()) {
            assert(out_size < 64);
            auto val = 1 << output.type.size();
            return std::make_unique<BinaryConstraint>(output, input, "mod", MyVariable::constant(std::to_string(val)));
        }
        return std::make_unique<UnaryConstraint>(output, input);
    }
}

// Create equality constraint for sext instruction
std::unique_ptr<UnaryConstraint> transform_sext(Instruction const * I) {
    return std::make_unique<UnaryConstraint>(convert_name_to_myvar(I), convert_name_to_myvar(I->getOperand(0)));
}

// Create constraint for logic instruction with boolean variables
std::unique_ptr<BinaryConstraint> transform_logic_operand(Instruction const * I) {
    auto op1_type = get_type(I->getOperand(0)->getType());
    auto op2_type = get_type(I->getOperand(1)->getType());

    if (isBoolLike(op1_type) and isBoolLike(op2_type)) {
        return transform_binary_inst(I);
    } else {
        throw std::logic_error("Logic operation not on Bool");
    }
}

} // namespace

// Create constraint for load instruction with global variable
std::unique_ptr<Equality> Context::transform_load_operand(Instruction const * I) {
    assert(llvm::isa<GlobalVariable>(I->getOperand(0)));
    auto * global_var = llvm::dyn_cast<GlobalVariable>(I->getOperand(0));
    if (not global_var) { throw std::logic_error("Unexpected operand of load instruction"); }
    auto it = global_vars.find(global_var);
    if (it == global_vars.end()) { throw std::logic_error("Global variable missing in our info"); }
    auto const & [name, index] = it->second;

    auto lhs = convert_name_to_myvar(I);
    auto type = get_type(I->getType());
    auto rhs = MyVariable::variable(name + "_" + std::to_string(index), type);

    return std::make_unique<Equality>(std::move(lhs), std::move(rhs));
}

// Create constraint for store instruction with global variable
std::unique_ptr<Equality> Context::transform_store_operand(Instruction const * I) {
    assert(llvm::isa<GlobalVariable>(I->getOperand(1)));
    auto * global_var = llvm::dyn_cast<GlobalVariable>(I->getOperand(1));
    if (not global_var) { throw std::logic_error("Unexpected operand of store instruction"); }
    auto it = global_vars.find(global_var);
    if (it == global_vars.end()) { throw std::logic_error("Global variable missing in our info"); }
    auto & [name, index] = it->second;
    ++index;
    auto lhs = MyVariable::variable(name + "_" + std::to_string(index), get_type(global_var->getValueType()));
    return std::make_unique<Equality>(std::move(lhs), convert_operand_to_myvar(I->getOperand(0)));
}

// Set variables for phi instruction, depending on label before
std::vector<std::unique_ptr<UnaryConstraint>> Context::transform_phi_instructions(MyBasicBlock const & predecessor,
                                                                                  MyBasicBlock const & successor) {

    std::vector<std::unique_ptr<UnaryConstraint>> result;

    for (Instruction const & I : successor.BB_link->instructionsWithoutDebug()) {
        if (I.getOpcode() == Instruction::PHI) {
            Value const * translation = I.DoPHITranslation(successor.BB_link, predecessor.BB_link);

            result.push_back(
                std::make_unique<UnaryConstraint>(convert_name_to_myvar(&I), convert_operand_to_myvar(translation)));
        }
    }
    return result;
}

// Transform instructions to constraints from instructions in basic block
Implication::Constraints Context::transform_instructions(MyBasicBlock const & BB, MyFunctionInfo & function_info) {

    Implication::Constraints result;
    function_info.e_index = 0;

    for (Instruction const & I : BB.BB_link->instructionsWithoutDebug()) {
        switch (I.getOpcode()) {
            // Instructions with no constraint
            case Instruction::Br:
            case Instruction::CallBr:
            case Instruction::IndirectBr:
            case Instruction::PHI:
            case Instruction::Ret:
            case Instruction::Unreachable:
            case Instruction::Switch:
                break;
            // Instructions with 1 constraint
            case Instruction::ICmp:
            case Instruction::Add:
            case Instruction::Sub:
            case Instruction::Mul:
            case Instruction::UDiv:
            case Instruction::SDiv:
            case Instruction::URem:
            case Instruction::SRem:
                result.push_back(transform_binary_inst(&I));
            break;
            case Instruction::ZExt:
                result.push_back(transform_zext(&I));
            break;
            case Instruction::Trunc:
                result.push_back(transform_trunc(&I));
            break;
            case Instruction::SExt:
                result.push_back(transform_sext(&I));
            break;
            case Instruction::Load:
                result.push_back(transform_load_operand(&I));
            break;
            case Instruction::Store:
                result.push_back(transform_store_operand(&I));
            break;
            case Instruction::Select: {
                result.push_back(transform_select(dyn_cast<SelectInst>(&I)));
                break;
            }
            // Transform logic instruction on booleans
            case Instruction::Xor:
            case Instruction::And:
            case Instruction::Or:
                result.push_back(transform_logic_operand(&I));
            break;
            case Instruction::Call: {
                auto predicates = transform_function_call(&I, function_info);
                std::move(predicates.begin(), predicates.end(), std::back_inserter(result));
                break;
            }
            default:
                throw UnsupportedFeature("Not implemented instruction: " + std::string(I.getOpcodeName()));
        }
    }
    return result;
}

namespace {
Implication::Constraints constraints_on_globals(MyFunctionInfo const & function_info, Context::GlobalInfo & global_info) {
    Implication::Constraints constraints;
    for (auto & [var, entry] : global_info) {
        auto & [name, index] = entry;
        ++index;
        auto type = get_type(var->getValueType());
        auto lhs = MyVariable::variable(name + "_" + std::to_string(index), type);
        auto rhs = function_info.is_main_function ? convert_operand_to_myvar(var->getInitializer()) : MyVariable::variable(name, type);
        constraints.push_back(std::make_unique<Equality>(lhs, rhs));
    }
    return constraints;
}

bool isRegisterValue(Value const  * V) {
    return V and (isa<Instruction>(V) or isa<Argument>(V));
}

std::vector<PHINode const *> collectPhiNodes(BasicBlock const & BB) {
    std::vector<PHINode const *> phis;
    for (Instruction const & I : BB) {
        if (auto * phi = dyn_cast<PHINode>(&I)) {
            phis.push_back(phi);
        } else {
            break; // PHI nodes are always at the beginning
        }
    }
    return phis;
}

} // namespace

/// Transfer to first basic block, we only need to make sure we have the right values of global variables
Implication Context::get_entry_block_implication(MyFunctionInfo const & function_info, MyBasicBlock const & BB1) {
    auto constraints = constraints_on_globals(function_info, global_vars);
    auto BB1_predicate = create_basic_block_predicate(BB1, BasicBlockPredicateType::ENTRY, function_info);
    return {std::move(BB1_predicate), std::move(constraints)};
}

// Create predicate for basic block: Format {name}({variables}), ex. BB1(%x1,%x2)
MyPredicate Context::create_basic_block_predicate(MyBasicBlock const & BB, BasicBlockPredicateType const type,
                                                  MyFunctionInfo const & function_info) {

    // Failed assert block
    if (BB.isFalseBlock) { return get_fail_block_predicate(function_info); }

    // Convert variables
    std::vector<MyVariable> vars;
    auto const & live_variables = type == BasicBlockPredicateType::ENTRY
                                ? function_info.liveness_info.live_in.at(BB.BB_link)
                                : function_info.liveness_info.live_out.at(BB.BB_link);

    auto processRegisterValue = [&](Value const * v) {
        assert(isRegisterValue(v));
        vars.push_back(convert_name_to_myvar(v));
    };
    // Function arguments need to be carried along
    for (auto const & arg : function_info.llvm_function.args()) {
        if (not live_variables.contains(&arg)) {
            processRegisterValue(&arg);
        }
    }

    for (auto const & v : live_variables) {
        processRegisterValue(v);
    }

    // Phi values must be part of the entry predicates
    if (type == BasicBlockPredicateType::ENTRY) {
        for (auto const * phi_value : collectPhiNodes(*BB.BB_link)) {
            processRegisterValue(phi_value);
        }
    }
    // Branching value must be part of the exit predicates
    if (type == BasicBlockPredicateType::EXIT) {
        Instruction const * terminator = BB.BB_link->getTerminator();
        if (auto * branch = dyn_cast<BranchInst>(terminator); branch and branch->isConditional()) {
            Value const * condition = branch->getCondition();
            if (isRegisterValue(condition)) { processRegisterValue(condition); }
        } else if (auto const * ret = dyn_cast<ReturnInst>(terminator)) {
            if (Value const * ret_value = ret->getReturnValue(); isRegisterValue(ret_value)) {
                processRegisterValue(ret_value);
            }
        }
    }

    add_global_variables(vars, function_info);

    return {BB.name + "_" + to_string(type), vars};
}

// Create current function predicate not for call instruction
MyPredicate Context::get_function_predicate(MyFunctionInfo const & function_info, MyVariable e_in, MyVariable e_out) {

    // Create predicate
    Function const & F = function_info.llvm_function;
    MyPredicate predicate{F.getName().str()};

    // Add parameters
    for (auto arg = F.arg_begin(); arg != F.arg_end(); ++arg) {
        predicate.vars.push_back(convert_name_to_myvar(arg));
    }

    // Add return value
    if (!F.getReturnType()->isVoidTy()) {
        assert(function_info.return_value.has_value());
        predicate.vars.push_back(function_info.return_value.value());
    }

    if (!function_info.is_main_function) {
        // Add input and output errors
        predicate.vars.push_back(e_in);
        predicate.vars.push_back(e_out);
    }
    add_global_variables(predicate.vars, function_info);
    return predicate;
}

// Return fail block predicate
MyPredicate Context::get_fail_block_predicate(MyFunctionInfo const & function_info) {
    if (function_info.is_main_function) {
        // Return new predicate if main function
        return MyPredicate(function_info.name + "_error");
    } else {
        // Return function predicate with output error
        return get_function_predicate(function_info, MyVariable::constant("false"), MyVariable::constant("true"));
    }
}

Implications toChc(Module const & module) {
    return ChcTransform{}.run(module);
}

Implications ChcTransform::run(Module const & module) {
    auto context = Context::create(module);
    for (Function const & f : module) {
        if (not f.isDeclaration()) { context.analyze(f); }
    }
    return context.finish();
}
} // namespace hornix