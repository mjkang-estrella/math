#!/bin/bash
# usage: run_gen.sh T K c1,c2 qmin   (runs from indep2/)
T=$1; K=$2; C=$3; Q=$4
out=certs_e/t${T}_K${K}_c${C/,/_}.jsonl
if [ -s "$out" ]; then exit 0; fi
E_UNIV=gen/univ_wide.json bash -c "ulimit -v 4000000; timeout 1100 python3 -I gen/gen_nd.py $out.tmp 3 $C $K $Q --deep 8 --mcap 1000000000" > logs/gen_t${T}_K${K}_c${C/,/_}.log 2>&1
rc=$?
if [ $rc -eq 0 ] && [ -s $out.tmp ]; then
  python3 -I - "$out.tmp" "$T" <<'PY'
import sys, json
f, T = sys.argv[1], int(sys.argv[2])
L = open(f).read().splitlines(); m = json.loads(L[0]); m['target'] = T
open(f[:-4], 'w').write('\n'.join([json.dumps(m)] + L[1:]) + '\n')
PY
fi
echo "t$T K$K c$C q$Q rc=$rc" >> logs/gen_summary.txt
