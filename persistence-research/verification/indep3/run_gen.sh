#!/bin/bash
# usage: run_gen.sh K c1,c2 qmin   (runs from indep3/); output certs_e2/K{K}_c{c1}_{c2}.jsonl
K=$1; C=$2; Q=$3
out=certs_e2/K${K}_c${C/,/_}.jsonl
if [ -s "$out" ]; then exit 0; fi
E_UNIV=gen/univ_wide.json PYTHONDONTWRITEBYTECODE=1 bash -c "ulimit -v 4000000; timeout 1150 python3 -I gen/gen_nd.py $out.tmp 3 $C $K $Q --deep 8 --mcap 1000000000" > logs/gen_K${K}_c${C/,/_}.log 2>&1
rc=$?
if [ $rc -eq 0 ] && [ -s $out.tmp ]; then mv $out.tmp $out; fi
echo "K$K c$C q$Q rc=$rc" >> logs/gen_summary.txt
