#!/bin/bash

if [ "$#" -ne 1 ]; then
    echo "Should be specified cpp file name"
fi

filename="$1"

# Extracting the file extension
extension="${filename##*.}"

# Checking if the extension is "cpp" or "c"
if [ "$extension" = "cpp" ]; then
  file_name=$(basename $1 .cpp)
  echo "(set-logic HORN)" > $file_name.smt2
  
  clang -Xclang -disable-O0-optnone -S -emit-llvm $1 -o $file_name.ll
  opt -passes=mem2reg -S $file_name.ll -o $file_name.ll
  opt -disable-output $file_name.ll -passes=chc-transform >> $file_name.smt2
  
  echo "(check-sat)" >> $file_name.smt2
  
  z3 -smt2 $file_name.smt2
  
  rm $file_name.ll $file_name.smt2

elif [ "$extension" = "c" ]; then
  file_name=$(basename $1 .c)
  cp $1 ./$file_name.cpp
  echo "(set-logic HORN)" > $file_name.smt2

  clang -Xclang -disable-O0-optnone -fbracket-depth=400 -S -emit-llvm $file_name.cpp -o $file_name.ll
  opt -passes=mem2reg -S $file_name.ll -o $file_name.ll
  opt -disable-output $file_name.ll -passes=chc-transform >> $file_name.smt2

  echo "(check-sat)" >> $file_name.smt2

  z3 -smt2 $file_name.smt2

  rm $file_name.ll $file_name.smt2 $file_name.cpp 
elif [ "$extension" = "i" ]; then
  file_name=$(basename $1 .i)
  cp $1 ./$file_name.cpp
  echo "(set-logic HORN)" > $file_name.smt2

  clang -Xclang -disable-O0-optnone -S -emit-llvm $file_name.cpp -o $file_name.ll
  opt -passes=mem2reg -S $file_name.ll -o $file_name.ll
  opt -disable-output $file_name.ll -passes=chc-transform >> $file_name.smt2

  echo "(check-sat)" >> $file_name.smt2

  z3 -smt2 $file_name.smt2

  rm $file_name.ll $file_name.smt2 $file_name.cpp 
else
  echo "$filename is neither a C++ nor a C file."
  exit
fi
