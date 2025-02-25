#!/bin/bash

if [ "$#" -ne 2 ]; then
    echo "Should be specified dir with set file and timeout"
    exit
fi

file="$1"
timeout="$2"

while read line; do
  if [[ "$line" =~ "#" ]]; then 
   continue 1
  else
   repo=$(echo "${line%%/*}")
   ./test-bench.sh "sv-benchmarks/c/$repo/" $timeout
  fi
done < $file
