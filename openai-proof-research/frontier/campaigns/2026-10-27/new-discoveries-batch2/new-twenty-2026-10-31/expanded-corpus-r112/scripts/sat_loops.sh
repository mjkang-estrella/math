#!/bin/bash
# Reproducible SAT loops (each cadical call capped at 25 s). usage: sat_loops.sh mindeg B NMAX | cutlemma A B | runs A B
cd "$(dirname "$0")/.."
C=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/cadical
T=tmp/loop.$$.cnf
case "$1" in
 mindeg) b=$2; for n in $(seq $b $3); do best=-1; for d in $(seq 0 $((n-1))); do python3 scripts/mindeg.py $n $b $d $T; r=$(timeout 25 $C -q $T | head -1); if [ "$r" = "s SATISFIABLE" ]; then best=$d; elif [ "$r" = "s UNSATISFIABLE" ]; then break; else best="$best(unknown at d=$d)"; break; fi; done; echo "b=$b n=$n maxmindeg=$best formula=$(python3 -c "import math;print($n-math.ceil($n/($b-2)))")"; done;;
 cutlemma) a=$2; b=$3; F=$(( (a-1)*(b-2) )); for n in $(seq 3 $F); do python3 scripts/cut_lemma.py $a $b $n $T >/dev/null; echo "a=$a b=$b n=$n $(timeout 25 $C -q $T | head -1)"; done;;
 runs) a=$2; b=$3; F=$(( (a-1)*(b-2) )); for n in $(seq $((a+1)) $F); do for rf in $(seq 0 $((a-1))); do python3 scripts/runs_test.py $a $b $n $rf $T; echo "a=$a b=$b n=$n rf=$rf $(timeout 25 $C -q $T | head -1)"; done; done;;
esac
rm -f $T
