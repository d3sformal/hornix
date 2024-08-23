#!/bin/bash

if [ "$#" -ne 2 ]; then
    echo "Should be specified dir with files name and timeout"
    exit
fi

files="$1"
timeout="$2"
dir_name="tmp"
dir="$(dirname $files)/" 

mkdir -p $dir_name

if [[ "$files" =~ "*" ]]; then 
   files=$(echo "${files%%\**}*.yml")
else 
   files=$(echo "${files}") 
fi

for f in $files;
 do 
 file_name=$(basename $f .yml)
 expected=$(sed -n '/unreach-call.prp/ {n;p}' $f)
 if [[ "$expected" =~ "true" ]]; then
    exp_res="sat"
 elif [[ "$expected" =~ "false" ]]; then
    exp_res="unsat"
 else
    echo "$file_name; ERROR - no unreach"
    continue 1
 fi

 if [ -f $dir$file_name.c ]; then 
   run_file=$dir$file_name.c
 elif [ -f $dir$file_name.i ]; then
   run_file=$dir$file_name.i
 else 
   echo "$file_name no .c or .i file"
   continue 1
 fi
  
 RESULT=$(timeout $timeout ./chc-transform.sh $run_file $dir_name);
 if [ $? -eq 124 ]; then 
    echo "$file_name; TOO LONG"
    continue 1
 fi

 if [ "$RESULT" = "sat" ]; then
    if [ "$RESULT" = "$exp_res" ]; then
        echo "$file_name; OK-sat"
    else
        echo "$file_name; BAD-sat" 
    fi
 elif [ "$RESULT" = "unsat" ]; then 
    if [ "$RESULT" = "$exp_res" ]; then
        echo "$file_name; OK-unsat"
    else
        echo "$file_name; BAD-unsat" 
    fi
 elif [ "$RESULT" = "error" ]; then 
    echo "$file_name; ERROR"
 else 
    echo "$file_name; unknown"
 fi
done

rm -r $dir_name
