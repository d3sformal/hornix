#!/bin/bash

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
test_dir="${script_dir}/benchmarks"
executable="${script_dir}/../build/src/hornix"
pass_count=0
fail_count=0
skip_count=0

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

# Iterate over each .c file in the directory
for bench in "${test_dir}"/*.c; do
  [[ -e "${bench}" ]] || continue  # Skip if no .c files

  BASENAME=$(basename "${bench}" .c)

  # Check if filename ends with "true" or "false"
  if [[ "$BASENAME" =~ (true|false)$ ]]; then
    EXPECTED="${BASH_REMATCH[1]}"
    
    OUTPUT="$(${executable} ${bench})"
    #echo ${OUTPUT}
    
    # Get the first word from the output
    FIRST_WORD=$(echo "$OUTPUT" | awk '{print tolower($1)}')
    if [[ "$FIRST_WORD" == "sat" ]]; then
        FIRST_WORD="true"
    fi
    if [[ "$FIRST_WORD" == "unsat" ]]; then
        FIRST_WORD="false"
    fi

    if [[ "$FIRST_WORD" == "true" || "$FIRST_WORD" == "false" ]]; then
      if [[ "$FIRST_WORD" == "$EXPECTED" ]]; then
        printf "%-30s ${GREEN}PASS${NC}\n" "${BASENAME}"
        ((pass_count++))
      else
        printf "%-30s ${RED}FAIL${NC}\n" "${BASENAME}"
        ((fail_count++))
      fi
    else
      printf "%-30s ${RED}FAIL${NC}\n" "${BASENAME}"
      ((fail_count++))
    fi
  else
    echo "Skipping: ${BASENAME} (filename doesn't end with 'true' or 'false')"
    ((skip_count++))
  fi
done

echo
echo "========== Summary =========="
echo -e "✅ Passed: ${GREEN}${pass_count}${NC}"
echo -e "❌ Failed: ${RED}${fail_count}${NC}"
echo -e "⏭️  Skipped: $skip_count"


# Exit with non-zero status if any test failed
if [[ $fail_count -gt 0 ]]; then
  exit 1
else
  exit 0
fi
