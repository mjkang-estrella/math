#!/bin/bash
# Re-run the whole independent audit.  Every python call is memory-limited.  Run from verification/ :  bash indep/run_all.sh
cd "$(dirname "$0")/.."
PY="python3 -I"
lim() { bash -c "ulimit -v 1500000; $*"; }
rm -f indep/certs/*.jsonl
echo "### soundness / unit tests"
lim "$PY indep/test_region.py"
lim "$PY /dev/stdin" <<'PYEOF'
import sys; sys.path.insert(0,'indep')
from nt import *
cnt=0
for K in [8,89,98,269,908,989,9008,17,26,116]:
    t0=vp(K,2)
    for k in range(t0+1,5):
        for ar in [(0,None),(2,None),(2,2),(3,3),(5,None),(1,1)]:
            for wr in [(0,None),(0,0),(1,None),(2,2),(6,None)]:
                assert pin_unsolvable(K,t0,k,ar,wr)==pin_unsolvable_bruteforce(K,t0,k,ar,wr); cnt+=1
print("pin_unsolvable (lattice/discrete-log) == brute force residue enumeration on",cnt,"cases")
PYEOF
echo "### agent's 2-D certificates under MY checker (check2d.py, written before reading the agent's checker)"
for f in glm/r8/cert2d_*.jsonl; do lim "$PY indep/check2d.py $f 200" 2>&1 | grep -E "^cert2d|RESULT|^     -|stats"; done
echo "### my generator + checker: 1-D (all-low constants and q=3 slices)"
for K in 98 107 116 188 197 278 908 917 926 989 998 1079 1169 1808 1817 1889 1979 2708 2789 9008 18008 27008 99008; do
  t=$(python3 -c "
K=$K; t=0
while K%2==0: K//=2; t+=1
print(t)")
  lim "$PY indep/gen_nd.py indep/certs/my1d_K$K.jsonl 1 '' $K $((t+1)) --deep 2 --mcap 1000000000 2>&1 | grep -E 'nodes=' | tr '\n' ' '; $PY indep/checknd.py indep/certs/my1d_K$K.jsonl 800 | grep -E 'RESULT|solutions in box' | tr '\n' ' '"; echo " [K=$K t0=$t domain L>=$((t+1))]"
done
echo "### my generator + checker: 2-D one-far (A,K,qmin)"
for spec in "9 8 4" "18 8 4" "27 8 4" "9 89 3" "18 89 3" "27 89 3" "9 98 3" "9 269 3" "9 908 3" "9 989 3" "9 9008 5"; do
  set -- $spec
  lim "$PY indep/gen_nd.py indep/certs/my2d_A$1_K$2.jsonl 2 $1 $2 $3 --deep 2 --mcap 1000000000 2>&1 | grep -E 'nodes=' | tr '\n' ' '; $PY indep/checknd.py indep/certs/my2d_A$1_K$2.jsonl 220 | grep -E 'RESULT|solutions in box' | tr '\n' ' '"; echo " [A=$1 K=$2 qmin=$3]"
done
echo "### my generator + checker: 3-D two-far {2,2,2}"
for spec in "8 4" "89 3"; do
  set -- $spec
  lim "$PY indep/gen_nd.py indep/certs/my3d_K$1.jsonl 3 9,9 $1 $2 --deep 2 --mcap 1000000000 2>&1 | grep -E 'nodes=' | tr '\n' ' '; $PY indep/checknd.py indep/certs/my3d_K$1.jsonl 160 | grep -E 'RESULT|solutions in box|stats' | tr '\n' ' '"; echo " [K=$1 q1min=$2]"
done
echo "### positive controls (a certificate for an equation WITH a solution must record it)"
for k in 683 2609; do
  r=13122; [ $k = 2609 ] && r=14406
  lim "$PY indep/gen_nd.py indep/certs/ctrl_A9_K$k.jsonl 2 9 $k 3 4,3 $r | grep -E 'nodes=|solutions' | tr '\n' ' '; $PY indep/checknd.py indep/certs/ctrl_A9_K$k.jsonl 150 | grep -E 'RESULT|solutions' | tr '\n' ' '"; echo
done
echo "### 3-D positive control + tamper tests"
lim "$PY indep/controls.py"
echo "### configuration coverage table"
lim "$PY indep/coverage.py"
echo "### digit-level brute force"
lim "$PY indep/brute_digits.py 220 80"
