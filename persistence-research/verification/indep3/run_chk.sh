#!/bin/bash
# usage: run_chk.sh cert.jsonl [box]   -> logs/chk_<name>.log, appends summary
f=$1; box=${2:-60}; b=$(basename $f .jsonl)
if grep -q '"five": true' <(head -1 $f); then C=chk5/checknd5.py; else C=chk/checknd.py; fi
bash -c "ulimit -v 4000000; PYTHONDONTWRITEBYTECODE=1 timeout 1100 python3 -I $C $f $box" > logs/chk_$b.log 2>&1
echo "$b rc=$? $(grep RESULT logs/chk_$b.log)" >> logs/chk_summary_$(basename $(dirname $f)).txt
