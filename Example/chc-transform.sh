#!/bin/bash

if [ "$#" -ne 2 ]; then
    echo "Should be specified cpp file name and tmp-dir name"
    exit
fi

filename="$1"
dir_name="$2"

mkdir -p $dir_name

# Extracting the file extension
extension="${filename##*.}"

# Checking if the extension is "cpp" or "c"
if [ "$extension" = "cpp" ]; then
  file_name=$(basename $1 .cpp)
  

elif [ "$extension" = "c" ]; then
  file_name=$(basename $1 .c)
elif [ "$extension" = "i" ]; then
  file_name=$(basename $1 .i)

else
  echo "$filename is neither a C++ nor a C file."
  exit
fi

clang -Xclang -disable-O0-optnone -S -fbracket-depth=400 -fdiscard-value-names -emit-llvm $1 -o $dir_name/$file_name.ll 2> /dev/null
if [ $? -gt 0 ]; then 
    echo "error"
    exit
fi 

RESULT=$(../build/src/hornix --solver z3 -i $dir_name/$file_name.ll)

if [ "$RESULT" = "sat" ]; then
  echo "safe"
elif [ "$RESULT" = "unsat" ]; then 
  echo "unsafe"
else 
  echo "unknown"
fi
