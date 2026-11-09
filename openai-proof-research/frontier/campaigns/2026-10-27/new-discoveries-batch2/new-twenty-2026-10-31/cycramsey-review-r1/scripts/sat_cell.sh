#!/bin/bash
# usage: sat_cell.sh a b n   (generate CNF, solve with CaDiCaL, verify SAT witnesses independently)
D="$(cd "$(dirname "$0")/.." && pwd)"; a=$1; b=$2; n=$3; f="$D/cnf/s$a-p$b-n$n.cnf"
python3 -I "$D/scripts/cnf.py" $a $b $n "$f"
/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical -q "$f" > "$D/tmp/s$a-p$b-n$n.sol"; rc=$?
echo "a=$a b=$b n=$n cadical_rc=$rc ($(head -c 200 "$D/tmp/s$a-p$b-n$n.sol" | grep -o 'UNSATISFIABLE\|SATISFIABLE' | head -1))"
if [ $rc = 10 ] && true; then python3 -I "$D/scripts/check_model.py" $a $b $n "$D/tmp/s$a-p$b-n$n.sol"; fi
rm -f "$f"
