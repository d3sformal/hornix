/*
 *  Copyright (c) 2024, Oliver Glitta <glittaoliver@gmail.com>
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: Apache-2.0
 */

#include "ChcTransform.hpp"

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
    void add_global_variables(MyPredicate & predicate, MyFunctionInfo const & function_info);

    void add_variable(Value const * var, MyBasicBlock & my_block);

    void set_basic_block_info(MyFunctionInfo * function_info);

    MyFunctionInfo load_my_function_info(Function const & F);

    Implication::Constraints transform_function_call(Instruction const * I, MyFunctionInfo & function_info);

    std::vector<Implication> transform_basic_blocks(MyFunctionInfo & function_info);

    Implication::Constraints transform_instructions(MyBasicBlock const & BB, MyFunctionInfo & function_info);

    std::unique_ptr<LoadConstraint> transform_load_operand(Instruction const * I);

    std::unique_ptr<Equality> transform_store_operand(Instruction const * I);

    std::vector<std::unique_ptr<UnaryConstraint>> transform_phi_instructions(MyBasicBlock const & predecessor,
                                                                             MyBasicBlock const & successor);

    Implication get_entry_block_implication(MyFunctionInfo const & function_info, MyBasicBlock const & BB1);

    MyPredicate create_basic_block_predicate(MyBasicBlock const & BB, bool isEntry,
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

void Context::analyze(Function const & F) {
    auto function_info = load_my_function_info(F);
    auto implications = transform_basic_blocks(function_info);
    std::move(implications.begin(), implications.end(), std::back_inserter(this->implications));
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

// Return variable to for end of the predicate if function is called in basic block
MyVariable get_function_call_var(MyBasicBlock const & BB, int e_index, MyBasicBlock const & successor) {
    if (BB.last_instruction != nullptr && BB.successors.size() > 0) {
        if (BB.successors.size() != 2 || successor.BB_link == BB.last_instruction->getOperand(2)) {
            return MyVariable::constant("false");
        } else {
            return MyVariable::variable("e" + std::to_string(e_index), "Bool");
        }
    } else {
        return MyVariable::constant("false");
    }
}

// Set variable in head predicate as prime when assigned new value in constraint
void set_prime_var_in_head(MyPredicate & head_predicate, std::string const & var_name) {
    for (auto & var : head_predicate.vars) {
        if (var.name == var_name) {
            var.isPrime = true;
            break;
        }
    }
}

// Get type of variable
std::string get_type(Type const * type) {
    if (type->isIntegerTy()) {
        auto w = cast<IntegerType>(type)->getBitWidth();
        return w == 1 ? "Bool" : "Int";
    }
    throw UnsupportedFeature("Unknown type of variable.");
}

std::string convert_name_to_string(Value const * const value) {
    std::string block_address;
    raw_string_ostream string_stream(block_address);

    value->printAsOperand(string_stream, false);

    return block_address;
}

// Convert operand to std::string, if negative string,
// return as function (-) with positive value (e.g. -100 => (- 100))
std::string convert_operand_to_string(Value const * value) {
    if (get_type(value->getType()) == "Int") {
        if (auto const * asConstant = dyn_cast<ConstantInt>(value)) {
            auto const num = asConstant->getSExtValue();
            if (num < 0) { return "(- " + std::to_string(num * -1) + ')'; }
            return std::to_string(num);
        }
    }

    return convert_name_to_string(value);
}

// Create constraint for br instruction
std::unique_ptr<UnaryConstraint> transform_br(Instruction const * I, BasicBlock const * successor) {
    // Instruction must have 3 operands to jump
    if (I->getNumOperands() != 3) { throw std::logic_error("Wrong instruction. Too few function operands."); }

    std::string res = successor == I->getOperand(2) ? "true" : "false";

    return std::make_unique<UnaryConstraint>(convert_name_to_string(I->getOperand(0)), res);
}

std::optional<std::int8_t> get_block_id_by_link(BasicBlock const * block,
                                                MyFunctionInfo::BasicBlocks const & my_blocks) {
    for (auto const & [id, my_block] : my_blocks) {
        if (my_block.BB_link == block) { return id; }
    }
    return std::nullopt;
}

} // namespace

MyFunctionInfo Context::load_my_function_info(Function const & F) {
    MyFunctionInfo function_info = load_basic_info(F);
    function_info.basic_blocks = load_basic_blocks(F);
    set_basic_block_info(&function_info);
    return function_info;
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
            auto current_exit_predicate = create_basic_block_predicate(BB, false, function_info);
            add_global_variables(current_exit_predicate, function_info);

            auto const & successor = function_info.basic_blocks.at(succ);
            auto succ_predicate = create_basic_block_predicate(successor, true, function_info);

            // Create implication
            Implication implication(succ_predicate);

            if (BB.isFunctionCalled) {
                current_exit_predicate.vars.push_back(get_function_call_var(BB, function_info.e_index, successor));
            }

            // Add current BB exit predicate
            implication.constraints.push_back(std::make_unique<MyPredicate>(current_exit_predicate));

            // Translate phi instructions
            for (auto && constraint : transform_phi_instructions(BB, successor)) {
                // Set prime variables
                set_prime_var_in_head(succ_predicate, constraint->result);
                constraint->result = constraint->result + PRIME_SIGN;
                implication.constraints.push_back(std::move(constraint));
            }

            // Branch predicate if 2 successors
            if (BB.last_instruction != nullptr && BB.successors.size() > 0) {
                if (BB.successors.size() == 2) {
                    auto br = transform_br(BB.last_instruction, successor.BB_link);
                    if ((br->result == "true" && br->value == "false") ||
                        (br->result == "false" && br->value == "true")) {
                        continue;
                        }
                    implication.constraints.push_back(std::move(br));
                }
            }

            if (not successor.isFalseBlock) { add_global_variables(succ_predicate, function_info); }
            implication.head = succ_predicate;
            clauses.push_back(std::move(implication));
        }

        // Add predicate if error in called function
        if (BB.isFunctionCalled) {
            auto fail = get_fail_block_predicate(function_info);
            Implication implication(fail);

            MyPredicate current_exit_predicate = create_basic_block_predicate(BB, false, function_info);
            add_global_variables(current_exit_predicate, function_info);
            current_exit_predicate.vars.push_back(MyVariable::constant("true"));
            implication.constraints.push_back(std::make_unique<MyPredicate>(current_exit_predicate));

            clauses.push_back(std::move(implication));
        }

        // From return instruction to function predicate implication
        if (BB.isLastBlock) {
            auto fun_predicate = get_function_predicate(function_info, MyVariable::constant("false"), MyVariable::constant("false"));

            auto implication = Implication(fun_predicate);

            MyPredicate current_exit_predicate = create_basic_block_predicate(BB, false, function_info);
            add_global_variables(current_exit_predicate, function_info);
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

// Add global variables to basic block predicate
void Context::add_global_variables(MyPredicate & predicate, MyFunctionInfo const & function_info) {
    for (auto const & [llvm_global, entry] : global_vars) {
        auto const & [name, index] = entry;
        if (not function_info.is_main_function) {
            // No main function needs input value of global variable
            predicate.vars.push_back(MyVariable::variable(name, "Int"));
        }
        predicate.vars.push_back(MyVariable::variable(name + "_" + std::to_string(index), "Int"));
    }
}



// Create implication from entry to exit point in basic block
Implication Context::create_entry_to_exit(MyBasicBlock const & BB, MyFunctionInfo & function_info) {

    MyPredicate entry_predicate = create_basic_block_predicate(BB, true, function_info);
    add_global_variables(entry_predicate, function_info);

    Implication::Constraints constraints = transform_instructions(BB, function_info);

    auto exit_predicate = create_basic_block_predicate(BB, false, function_info);
    add_global_variables(exit_predicate, function_info);

    // Add last output error variable if some function called in BB
    if (BB.isFunctionCalled) {
        exit_predicate.vars.push_back(MyVariable::variable("e" + std::to_string(function_info.e_index), "Bool"));
    }

    std::unordered_set<std::string> prime_vars;

    // Create prime variables in predicates when new assignment
    for (auto & constraint : constraints) {

        if (FunctionPredicate * fp = dynamic_cast<FunctionPredicate *>(constraint.get())) {

            set_prime_var_in_head(exit_predicate, fp->changed_var);
            prime_vars.insert(fp->changed_var);

            // Set variables when assigned
            for (unsigned int i = 0; i < fp->vars.size(); i++) {
                if (prime_vars.find(fp->vars[i].name) != prime_vars.end()) { fp->vars[i].isPrime = true; }
            }
        } else if (BinaryConstraint * bc = dynamic_cast<BinaryConstraint *>(constraint.get())) {

            // Set operands when assigned before
            if (prime_vars.find(bc->operand1) != prime_vars.end()) { bc->operand1 = bc->operand1 + PRIME_SIGN; }
            if (prime_vars.find(bc->operand2) != prime_vars.end()) { bc->operand2 = bc->operand2 + PRIME_SIGN; }

            // Set assigned variable as prime in current constraint and head predicate
            set_prime_var_in_head(exit_predicate, bc->result);
            prime_vars.insert(bc->result);
            bc->result = bc->result + PRIME_SIGN;
        }

        else if (UnaryConstraint * uc = dynamic_cast<UnaryConstraint *>(constraint.get())) {

            // Set operands when assigned before
            if (prime_vars.find(uc->value) != prime_vars.end()) { uc->value = uc->value + PRIME_SIGN; }

            // Set assigned variable as prime in current constraint and head predicate
            set_prime_var_in_head(exit_predicate, uc->result);
            prime_vars.insert(uc->result);
            uc->result = uc->result + PRIME_SIGN;
        }

        else if (ITEConstraint * ite = dynamic_cast<ITEConstraint *>(constraint.get())) {

            // Set operands as prime when assigned before
            if (prime_vars.find(ite->condition) != prime_vars.end()) { ite->condition = ite->condition + PRIME_SIGN; }
            if (prime_vars.find(ite->operand1) != prime_vars.end()) { ite->operand1 = ite->operand1 + PRIME_SIGN; }
            if (prime_vars.find(ite->operand2) != prime_vars.end()) { ite->operand2 = ite->operand2 + PRIME_SIGN; }

            // Set assigned variable as prime in current constraint and head predicate
            set_prime_var_in_head(exit_predicate, ite->result);
            prime_vars.insert(ite->result);
            ite->result = ite->result + PRIME_SIGN;
        }

        else if (LoadConstraint * lc = dynamic_cast<LoadConstraint *>(constraint.get())) {

            // Set assigned variable as prime in current constraint and head predicate
            set_prime_var_in_head(exit_predicate, lc->result);
            prime_vars.insert(lc->result);
            lc->result = lc->result + PRIME_SIGN;
        }

        else if (auto * sc = dynamic_cast<Equality *>(constraint.get())) {

            // Set operand as prime when assigned before
            if (prime_vars.find(sc->value) != prime_vars.end()) { sc->value = sc->value + PRIME_SIGN; }
        }
    }
    constraints.push_back(std::make_unique<MyPredicate>(entry_predicate));
    Implication implication(exit_predicate);
    implication.constraints = std::move(constraints);
    return implication;
}

void Context::set_basic_block_info(MyFunctionInfo * function_info) {
    for (auto & it : function_info->basic_blocks) {
        MyBasicBlock & BB = it.second;
        BasicBlock const * block_link = BB.BB_link;

        // Set Predecessors of blocks and variables from them
        for (auto pred : predecessors(block_link)) {
            // Find predecessor id
            auto maybe_pred_id = get_block_id_by_link(pred, function_info->basic_blocks);
            if (maybe_pred_id.has_value()) {
                auto pred_id = maybe_pred_id.value();
                // Add predecessor
                BB.predecessors.push_back(pred_id);

                // Add new variables from predecessor
                for (auto v : function_info->basic_blocks.at(pred_id).vars) {
                    add_variable(v, BB);
                }
            }
        }

        // First basic block without predecessors load function arguments
        if (predecessors(block_link).empty()) {
            Function const & F = function_info->llvm_function;
            // Load arguments as variables
            for (auto arg = F.arg_begin(); arg != F.arg_end(); ++arg) {
                add_variable(arg, BB);
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

            // Remember last br instruction (should be only one)
            if (I.getOpcode() == Instruction::Br) { BB.last_instruction = &I; }

            // Remember return value of function
            if (I.getOpcode() == Instruction::Ret) {
                if (not function_info->llvm_function.getReturnType()->isVoidTy()) {
                    auto o = I.getOperand(0);
                    if (o->getValueID() == Value::ConstantIntVal) {
                        function_info->return_value = MyVariable::constant(convert_operand_to_string(o));
                    } else {
                        function_info->return_value = MyVariable::variable(convert_name_to_string(o), get_type(o->getType()));
                    }
                }
                BB.isLastBlock = true;
            }

            // Add instructions returning void
            if (not I.getType()->isVoidTy()) { add_variable(&I, BB); }

            // Add all variables from instruction
            for (auto & o : I.operands()) {
                add_variable(o, BB);
            }
        }
    }
}

// Set name for variable and add to basic block info if not presented
void Context::add_variable(Value const * var, MyBasicBlock & my_block) {
    // Skip labels and pointers
    if (var->getType()->isLabelTy() or var->getType()->isPointerTy()) { return; }
    my_block.vars.insert(var);
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

            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), ">=", "0"));
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), "<=", "4294967295"));
        } else if (function_name.find(UNSIGNED_SHORT_FUNCTION, 0) != std::string::npos) {
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), ">=", "(- 32768)"));
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), "<=", "32767"));
        } else if (function_name.find(UNSIGNED_USHORT_FUNCTION, 0) != std::string::npos) {
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), ">=", "0"));
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), "<=", "65535"));

        } else if (function_name.find(UNSIGNED_UCHAR_FUNCTION, 0) != std::string::npos) {

            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), ">=", "0"));
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), "<=", "255"));

        } else if (function_name.find(UNSIGNED_CHAR_FUNCTION, 0) != std::string::npos) {

            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), ">=", "(- 128)"));
            result.push_back(std::make_unique<ComparisonConstraint>(convert_name_to_string(I), "<=", "127"));

        } else {
            // If no predefined function, ignore call and add true constraint
            result.push_back(std::make_unique<MyPredicate>("true"));
        }
        return result;
    }

    auto predicate = std::make_unique<FunctionPredicate>(function_name);

    // Add parameters
    for (auto arg = call_inst->arg_begin(); arg != call_inst->arg_end(); ++arg) {
        if (arg->get()->getValueID() != Value::ConstantIntVal) {
            std::string var_name = convert_name_to_string(arg->get());
            std::string var_type = get_type(arg->get()->getType());

            predicate->vars.push_back(MyVariable::variable(std::move(var_name), std::move(var_type)));
        } else {
            predicate->vars.push_back(MyVariable::constant(convert_operand_to_string(arg->get())));
        }
    }

    // Add return variable
    if (!fn->getReturnType()->isVoidTy()) {
        std::string var_name = convert_name_to_string(I);

        predicate->vars.push_back(MyVariable::prime_variable(var_name, get_type(fn->getReturnType())));
        predicate->changed_var = var_name;
    }

    // Add variables for input error variable
    if (function_info.e_index == 0) {
        predicate->vars.push_back(MyVariable::constant("false"));
    } else {
        predicate->vars.push_back(MyVariable::variable("e" + std::to_string(function_info.e_index), "Bool"));
    }

    // Add variables for output error variable
    ++function_info.e_index;
    predicate->vars.push_back(MyVariable::variable("e" + std::to_string(function_info.e_index), "Bool"));

    // Add global variables input and output values
    for (auto & [var, entry] : global_vars) {
        auto & [name, index] = entry;
        predicate->vars.push_back(MyVariable::variable(name + "_" + std::to_string(index), "Int"));
        index++;
        predicate->vars.push_back(MyVariable::variable(name + "_" + std::to_string(index), "Int"));
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
    auto asString = [&](Value * val) -> std::string {
        if (auto asConstant = dyn_cast<ConstantInt>(val)) {
            if (comparison->isSigned()) {
                auto value = asConstant->getSExtValue();
                if (value < 0) { return "(- " + std::to_string(value * -1) + ')'; }
                return std::to_string(value);
            } else {
                auto value = asConstant->getZExtValue();
                return std::to_string(value);
            }
        }
        return convert_name_to_string(val);
    };

    return std::make_unique<BinaryConstraint>(convert_name_to_string(comparison), asString(lhs), sign, asString(rhs));
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

    return std::make_unique<BinaryConstraint>(convert_name_to_string(I), convert_operand_to_string(I->getOperand(0)),
                                              sign, convert_operand_to_string(I->getOperand(1)));
}

// Create constraint for zext instruction
std::unique_ptr<MyConstraint> transform_zext(Instruction const * I) {
    MyVariable input = MyVariable::variable(convert_name_to_string(I->getOperand(0)), get_type(I->getOperand(0)->getType()));
    MyVariable output = MyVariable::variable(convert_name_to_string(I), get_type(I->getType()));

    if (input.type == "Bool" && output.type == "Int") {
        return std::make_unique<ITEConstraint>(output.name, input.name, "1", "0");
    } else {
        return std::make_unique<UnaryConstraint>(output.name, input.name);
    }
}

std::unique_ptr<MyConstraint> transform_select(SelectInst const * I) {
    return std::make_unique<ITEConstraint>(
        convert_name_to_string(I),
        convert_operand_to_string(I->getCondition()),
        convert_operand_to_string(I->getTrueValue()),
        convert_operand_to_string(I->getFalseValue())
    );
}

// Create constraint for trunc instruction
std::unique_ptr<MyConstraint> transform_trunc(Instruction const * I) {
    MyVariable input = MyVariable::variable(convert_name_to_string(I->getOperand(0)), get_type(I->getOperand(0)->getType()));
    MyVariable output = MyVariable::variable(convert_name_to_string(I), get_type(I->getType()));

    if (input.type == "Int" && output.type == "Bool") {
        return std::make_unique<BinaryConstraint>(output.name, input.name, "!=", "0");
    } else {
        return std::make_unique<UnaryConstraint>(output.name, input.name);
    }
}

// Create equality constraint for sext instruction
std::unique_ptr<UnaryConstraint> transform_sext(Instruction const * I) {
    return std::make_unique<UnaryConstraint>(convert_name_to_string(I), convert_name_to_string(I->getOperand(0)));
}

// Create constraint for logic instruction with boolean variables
std::unique_ptr<BinaryConstraint> transform_logic_operand(Instruction const * I) {
    auto op1_type = get_type(I->getOperand(0)->getType());
    auto op2_type = get_type(I->getOperand(1)->getType());

    if (op1_type == "Bool" && op2_type == "Bool") {
        return transform_binary_inst(I);
    } else {
        throw std::logic_error("Logic operation not on Bool");
    }
}

} // namespace

// Create constraint for load instruction with global variable
std::unique_ptr<LoadConstraint> Context::transform_load_operand(Instruction const * I) {
    assert(llvm::isa<GlobalVariable>(I->getOperand(0)));
    auto * global_var = llvm::dyn_cast<GlobalVariable>(I->getOperand(0));
    if (not global_var) { throw std::logic_error("Unexpected operand of load instruction"); }
    auto it = global_vars.find(global_var);
    if (it == global_vars.end()) { throw std::logic_error("Global variable missing in our info"); }
    auto const & [name, index] = it->second;

    auto result = convert_name_to_string(I);
    auto value = name + "_" + std::to_string(index);

    return std::make_unique<LoadConstraint>(std::move(result), std::move(value));
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
    return std::make_unique<Equality>(name + "_" + std::to_string(index),
                                             convert_operand_to_string(I->getOperand(0)));
}

// Set variables for phi instruction, depending on label before
std::vector<std::unique_ptr<UnaryConstraint>> Context::transform_phi_instructions(MyBasicBlock const & predecessor,
                                                                                  MyBasicBlock const & successor) {

    std::vector<std::unique_ptr<UnaryConstraint>> result;

    for (Instruction const & I : successor.BB_link->instructionsWithoutDebug()) {
        if (I.getOpcode() == Instruction::PHI) {
            Value const * translation = I.DoPHITranslation(successor.BB_link, predecessor.BB_link);

            result.push_back(
                std::make_unique<UnaryConstraint>(convert_name_to_string(&I), convert_operand_to_string(translation)));
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
                throw UnsupportedFeature("Not implemented instruction");
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
        auto result = name + "_" + std::to_string(index);
        auto value = function_info.is_main_function ? convert_operand_to_string(var->getInitializer()) : name;
        constraints.push_back(std::make_unique<Equality>(result, value));
    }
    return constraints;
}
} // namespace

/// Transfer to first basic block, we only need to make sure we have the right values of global variables
Implication Context::get_entry_block_implication(MyFunctionInfo const & function_info, MyBasicBlock const & BB1) {
    auto constraints = constraints_on_globals(function_info, global_vars);
    auto BB1_predicate = create_basic_block_predicate(BB1, true, function_info);
    if (!BB1.isFalseBlock) { add_global_variables(BB1_predicate, function_info); }
    return {std::move(BB1_predicate), std::move(constraints)};
}

// Create predicate for basic block: Format {name}({variables}), ex. BB1(%x1,%x2)
MyPredicate Context::create_basic_block_predicate(MyBasicBlock const & BB, bool isEntry,
                                                  MyFunctionInfo const & function_info) {

    // Failed assert block
    if (BB.isFalseBlock) { return get_fail_block_predicate(function_info); }

    // Convert variables
    std::vector<MyVariable> vars;
    for (auto & v : BB.vars) {
        if (v->getValueID() != Value::ConstantIntVal) {
            std::string var_name = convert_name_to_string(v);
            std::string var_type = get_type(v->getType());

            vars.push_back(MyVariable::variable(std::move(var_name), std::move(var_type)));
        }
    }

    std::string suffix = isEntry ? "_entry" : "_exit";
    return {BB.name + suffix, vars};
}

// Create current function predicate not for call instruction
MyPredicate Context::get_function_predicate(MyFunctionInfo const & function_info, MyVariable e_in, MyVariable e_out) {

    // Create predicate
    Function const & F = function_info.llvm_function;
    MyPredicate predicate{F.getName().str()};

    // Add parameters
    for (auto arg = F.arg_begin(); arg != F.arg_end(); ++arg) {
        if (arg->getValueID() != Value::ConstantIntVal) {
            std::string var_name = convert_name_to_string(arg);
            std::string var_type = get_type(arg->getType());

            predicate.vars.push_back(MyVariable::variable(std::move(var_name), std::move(var_type)));
        }
    }

    // Add return value
    if (!F.getReturnType()->isVoidTy()) { predicate.vars.push_back(function_info.return_value); }

    if (!function_info.is_main_function) {
        // Add input and output errors
        predicate.vars.push_back(e_in);
        predicate.vars.push_back(e_out);
    }

    add_global_variables(predicate, function_info);

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