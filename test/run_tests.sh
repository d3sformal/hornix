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

check_unsupported_feature() {
  local benchmark="${script_dir}/unsupported/non_global_store.c"
  local output status
  output="$(${executable} --integer-theory bitvectors --print-chc "${benchmark}" 2>&1)"
  status=$?

  if [[ ${status} -eq 1 && "${output}" == *"Stores through non-global pointers are not supported."* ]]; then
    printf "%-48s ${GREEN}PASS${NC}\n" "Unsupported non-global store is rejected"
    ((pass_count++))
  else
    printf "%-48s ${RED}FAIL${NC} (exit %s: %s)\n" "Unsupported non-global store is rejected" "${status}" "${output}"
    ((fail_count++))
  fi
}

run_suite "${script_dir}/benchmarks" int
run_suite "${script_dir}/benchmarks" bitvectors
run_suite "${script_dir}/bitvectors" bitvectors

# This benchmark distinguishes the two theories: unbounded Int arithmetic
# proves x + 1 > x, while i8 bit-vectors expose the x = 255 counterexample.
run_benchmark "${script_dir}/bitvectors/overflow_false.ll" true int
check_bitvector_encoding
check_unsupported_feature

echo
echo "========== Summary =========="
echo -e "Passed: ${GREEN}${pass_count}${NC}"
echo -e "Failed: ${RED}${fail_count}${NC}"

if [[ ${fail_count} -gt 0 ]]; then
  exit 1
fi
