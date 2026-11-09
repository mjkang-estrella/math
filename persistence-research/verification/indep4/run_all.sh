#!/bin/bash
# usage: run_all.sh listfile outdir [brute]
list=$1; out=$2; br=${3:-11}
mkdir -p $out
cat $list | xargs -P 16 -I{} bash -c 'f={}; b=$(basename $(dirname $f))_$(basename $f .jsonl); ulimit -v 8000000; timeout 1700 python3 -I check_sym_F.py $f '$br' --json > '$out'/$b.json 2> '$out'/$b.err; echo "$b $?" >> '$out'/exit.txt'
