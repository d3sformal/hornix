#!/bin/bash

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
executable="${script_dir}/../build/src/hornix"
pass_count=0
fail_count=0

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

run_benchmark() {
  local bench="$1"
  local expected="$2"
  local theory="$3"
  local name
  name="$(basename "${bench}") [${theory}]"

  local output actual
  output="$(${executable} --integer-theory "${theory}" "${bench}" 2>&1)"
  actual="$(awk 'NR == 1 {print tolower($1)}' <<< "${output}")"
  case "${actual}" in
    sat) actual=true ;;
    unsat) actual=false ;;
  esac

  if [[ "${actual}" == "${expected}" ]]; then
    printf "%-48s ${GREEN}PASS${NC}\n" "${name}"
    ((pass_count++))
  else
    printf "%-48s ${RED}FAIL${NC} (expected %s, got %s)\n" "${name}" "${expected}" "${actual:-no result}"
    ((fail_count++))
  fi
}

run_suite() {
  local directory="$1"
  local theory="$2"
  local bench basename expected
  shopt -s nullglob
  for bench in "${directory}"/*.c "${directory}"/*.ll; do
    basename="$(basename "${bench}")"
    basename="${basename%.*}"
    if [[ "${basename}" =~ (true|false)$ ]]; then
      expected="${BASH_REMATCH[1]}"
      run_benchmark "${bench}" "${expected}" "${theory}"
    fi
  done
  shopt -u nullglob
}

check_bitvector_encoding() {
  local benchmark="${script_dir}/bitvectors/integer_instructions_true.ll"
  local output operator
  output="$(${executable} --integer-theory bitvectors --print-chc "${benchmark}" 2>&1)"

  for operator in '(_ BitVec 8)' 'bvadd' 'bvsub' 'bvmul' 'bvudiv' 'bvsdiv' 'bvurem' 'bvsrem' \
                  'bvand' 'bvor' 'bvxor' 'bvshl' 'bvlshr' 'bvashr' \
                  'bvult' 'bvule' 'bvugt' 'bvuge' 'bvslt' 'bvsle' 'bvsgt' 'bvsge' \
                  'zero_extend' 'sign_extend' 'extract'; do
    if grep -Fq "${operator}" <<< "${output}"; then
      printf "%-48s ${GREEN}PASS${NC}\n" "SMT emission: ${operator}"
      ((pass_count++))
    else
      printf "%-48s ${RED}FAIL${NC}\n" "SMT emission: ${operator}"
      ((fail_count++))
    fi
  done
}

check_local_array_encoding() {
  local benchmark="${script_dir}/arrays/local_array_false.c"
  local output operator
  output="$(${executable} --integer-theory bitvectors --print-chc "${benchmark}" 2>&1)"

  for operator in '(Array ' '(select ' '(store ' '(bvult '; do
    if grep -Fq "${operator}" <<< "${output}"; then
      printf "%-48s ${GREEN}PASS${NC}\n" "Local-array SMT emission: ${operator}"
      ((pass_count++))
    else
      printf "%-48s ${RED}FAIL${NC}\n" "Local-array SMT emission: ${operator}"
      ((fail_count++))
    fi
  done
}

check_unsupported_feature() {
  local benchmark="${script_dir}/unsupported/non_global_store.c"
  local output status
  output="$(${executable} --integer-theory bitvectors --print-chc "${benchmark}" 2>&1)"
  status=$?

  if [[ ${status} -eq 1 && "${output}" == *"Loads and stores require a non-escaping local array pointer."* ]]; then
    printf "%-48s ${GREEN}PASS${NC}\n" "Unsupported non-global store is rejected"
    ((pass_count++))
  else
    printf "%-48s ${RED}FAIL${NC} (exit %s: %s)\n" "Unsupported non-global store is rejected" "${status}" "${output}"
    ((fail_count++))
  fi
}

check_local_array_pointer_escape() {
  local benchmark="${script_dir}/unsupported/local_array_pointer_escape.c"
  local output status
  output="$(${executable} --integer-theory bitvectors --print-chc "${benchmark}" 2>&1)"
  status=$?

  if [[ ${status} -eq 1 && "${output}" == *"Pointer arguments are not supported in the local-array fragment."* ]]; then
    printf "%-48s ${GREEN}PASS${NC}\n" "Local-array pointer escape is rejected"
    ((pass_count++))
  else
    printf "%-48s ${RED}FAIL${NC} (exit %s: %s)\n" "Local-array pointer escape is rejected" "${status}" "${output}"
    ((fail_count++))
  fi
}

check_solver_failure() {
  local output status
  output="$(${executable} --solver false "${script_dir}/benchmarks/max_true.c" 2>&1)"
  status=$?

  if [[ ${status} -eq 1 && "${output}" == *"Solver 'false' exited with status 1"* ]]; then
    printf "%-48s ${GREEN}PASS${NC}\n" "Solver failures are reported"
    ((pass_count++))
  else
    printf "%-48s ${RED}FAIL${NC} (exit %s: %s)\n" "Solver failures are reported" "${status}" "${output}"
    ((fail_count++))
  fi
}

check_violation_witness() {
  local property="${script_dir}/witnesses/unreach-call.prp"
  local unsafe="${script_dir}/witnesses/unsafe_unreach.c"
  local safe="${script_dir}/witnesses/safe_unreach.c"
  local witness unsafe_output safe_output expected_hash
  witness="$(mktemp)"

  unsafe_output="$(${executable} --integer-theory bitvectors --data-model LP64 --property "${property}" \
    --witness-output "${witness}" "${unsafe}" 2>&1)"
  expected_hash="$(sha256sum "${unsafe}" | awk '{print $1}')"
  if [[ "${unsafe_output}" == unsat* ]] && python3 - "${witness}" "${expected_hash}" <<'PY'
import sys
import yaml

with open(sys.argv[1], encoding="utf-8") as stream:
    witness = yaml.safe_load(stream)

entry = witness[0]
metadata = entry["metadata"]
target = entry["content"][0]["segment"][0]["waypoint"]
assert entry["entry_type"] == "violation_sequence"
assert metadata["format_version"] == "2.2"
assert metadata["task"]["input_file_hashes"]["unsafe_unreach.c"] == sys.argv[2]
assert metadata["task"]["data_model"] == "LP64"
assert target["type"] == "target" and target["action"] == "follow"
assert target["location"] == {"file_name": "unsafe_unreach.c", "line": 6, "column": 5}
PY
  then
    printf "%-48s ${GREEN}PASS${NC}\n" "Violation witness for unsafe program"
    ((pass_count++))
  else
    printf "%-48s ${RED}FAIL${NC} (%s)\n" "Violation witness for unsafe program" "${unsafe_output}"
    ((fail_count++))
  fi

  rm -f "${witness}"
  safe_output="$(${executable} --integer-theory bitvectors --data-model LP64 --property "${property}" \
    --witness-output "${witness}" "${safe}" 2>&1)"
  if [[ "${safe_output}" == sat* ]] && [[ ! -e "${witness}" ]]; then
    printf "%-48s ${GREEN}PASS${NC}\n" "No witness for safe program"
    ((pass_count++))
  else
    printf "%-48s ${RED}FAIL${NC} (%s)\n" "No witness for safe program" "${safe_output}"
    ((fail_count++))
  fi

  rm -f "${witness}"
}

check_local_array_violation_witness() {
  local property="${script_dir}/witnesses/unreach-call.prp"
  local unsafe="${script_dir}/witnesses/local_array_unsafe_unreach.c"
  local witness output
  witness="$(mktemp)"

  output="$(${executable} --integer-theory bitvectors --data-model ILP32 --property "${property}" \
    --witness-format 2.1 --witness-output "${witness}" "${unsafe}" 2>&1)"
  if [[ "${output}" == unsat* ]] && grep -Fq 'format_version: "2.1"' "${witness}" && \
     grep -Fq 'type: target' "${witness}"; then
    printf "%-48s ${GREEN}PASS${NC}\n" "Violation witness for local array"
    ((pass_count++))
  else
    printf "%-48s ${RED}FAIL${NC} (%s)\n" "Violation witness for local array" "${output}"
    ((fail_count++))
  fi
  rm -f "${witness}"
}

check_witness_option_validation() {
  local property="${script_dir}/witnesses/unreach-call.prp"
  local unsafe="${script_dir}/witnesses/unsafe_unreach.c"
  local witness output status
  witness="$(mktemp)"

  output="$(${executable} --integer-theory int --data-model LP64 --property "${property}" \
    --witness-output "${witness}" "${unsafe}" 2>&1)"
  status=$?
  if [[ ${status} -eq 1 && "${output}" == *"Violation witnesses currently require --integer-theory bitvectors."* ]]; then
    printf "%-48s ${GREEN}PASS${NC}\n" "Witness requires bit-vector theory"
    ((pass_count++))
  else
    printf "%-48s ${RED}FAIL${NC} (exit %s: %s)\n" "Witness requires bit-vector theory" "${status}" "${output}"
    ((fail_count++))
  fi

  output="$(${executable} --integer-theory bitvectors --data-model LP64 --property "${property}" \
    --witness-output "${witness}" --print-ir "${unsafe}" 2>&1)"
  status=$?
  if [[ ${status} -eq 1 && "${output}" == *"--witness-output cannot be combined with --print-ir or --print-chc."* ]]; then
    printf "%-48s ${GREEN}PASS${NC}\n" "Witness rejects print modes"
    ((pass_count++))
  else
    printf "%-48s ${RED}FAIL${NC} (exit %s: %s)\n" "Witness rejects print modes" "${status}" "${output}"
    ((fail_count++))
  fi
  rm -f "${witness}"
}

check_witness_format_selection() {
  local property="${script_dir}/witnesses/unreach-call.prp"
  local unsafe="${script_dir}/witnesses/unsafe_unreach.c"
  local witness output status
  witness="$(mktemp)"

  output="$(${executable} --integer-theory bitvectors --data-model LP64 --property "${property}" \
    --witness-format 2.1 --witness-output "${witness}" "${unsafe}" 2>&1)"
  if [[ "${output}" == unsat* ]] && grep -Fq 'format_version: "2.1"' "${witness}"; then
    printf "%-48s ${GREEN}PASS${NC}\n" "Witness format 2.1 is selected"
    ((pass_count++))
  else
    printf "%-48s ${RED}FAIL${NC} (%s)\n" "Witness format 2.1 is selected" "${output}"
    ((fail_count++))
  fi

  rm -f "${witness}"
  output="$(${executable} --witness-format 2.3 "${unsafe}" 2>&1)"
  status=$?
  if [[ ${status} -eq 1 && "${output}" == *"--witness-format requires --witness-output."* ]]; then
    printf "%-48s ${GREEN}PASS${NC}\n" "Witness format requires output mode"
    ((pass_count++))
  else
    printf "%-48s ${RED}FAIL${NC} (exit %s: %s)\n" "Witness format requires output mode" "${status}" "${output}"
    ((fail_count++))
  fi
}

run_suite "${script_dir}/benchmarks" int
run_suite "${script_dir}/benchmarks" bitvectors
run_suite "${script_dir}/bitvectors" bitvectors
run_suite "${script_dir}/arrays" int
run_suite "${script_dir}/arrays" bitvectors

# This benchmark distinguishes the two theories: unbounded Int arithmetic
# proves x + 1 > x, while i8 bit-vectors expose the x = 255 counterexample.
run_benchmark "${script_dir}/bitvectors/overflow_false.ll" true int
check_bitvector_encoding
check_local_array_encoding
check_unsupported_feature
check_local_array_pointer_escape
check_solver_failure
check_violation_witness
check_local_array_violation_witness
check_witness_option_validation
check_witness_format_selection

echo
echo "========== Summary =========="
echo -e "Passed: ${GREEN}${pass_count}${NC}"
echo -e "Failed: ${RED}${fail_count}${NC}"

if [[ ${fail_count} -gt 0 ]]; then
  exit 1
fi
