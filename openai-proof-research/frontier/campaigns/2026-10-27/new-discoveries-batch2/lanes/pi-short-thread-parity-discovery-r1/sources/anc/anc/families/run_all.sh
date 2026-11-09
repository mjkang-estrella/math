#!/bin/bash
# Re-runs every finite verification used in Section 8 of the paper.
# Sequential and niced; about 20-40 minutes in total, depending on the machine.  Usage:  bash run_all.sh
set -u
cd "$(dirname "$0")"
mkdir -p logs
echo "== verify23.py: Table 6 / Theorem 8.5 for r <= 100, Gamma(i;{2*,3*}) = 3, g(S(2,3,z)) for z <= 160"
nice python3 verify23.py 100 160 | tee logs/verify23.log | tail -3
echo "== independent cross-check with the positional C++ solver famstates.cpp"
g++ -O2 -o famstates famstates.cpp
[ -f fs23_3000.txt ] || nice ./famstates 2 3 3000 > fs23_3000.txt
nice python3 crosscheck_table.py | tee logs/crosscheck_table.log
echo "== certify_gen.py: hypotheses of Lemmas 8.8, 8.9 and Proposition 8.11 for all pairs of Theorem 8.12"
: > logs/certify_all.log
pairs=""
for y in $(seq 3 14); do for x in $(seq 1 $((y-1))); do
  if [ $x -eq 1 ] && [ $((y%2)) -eq 0 ]; then continue; fi
  if [ $y -ge 13 ] && [ $x -gt 7 ]; then continue; fi
  pairs="$pairs $x,$y"; done; done
for y in $(seq 15 40); do pairs="$pairs 2,$y"; done
for pr in $pairs; do
  x=${pr%,*}; y=${pr#*,}
  RM=160; if [ "$x,$y" = "2,33" ]; then RM=200; fi     # R_1 - 1 = 160, except 200 for (2,33)
  nice python3 certify_gen.py $x $y $RM > logs/gen_${x}_${y}.log 2>&1
  echo "($x,$y) R1-1=$RM $(grep RESULT logs/gen_${x}_${y}.log)" | tee -a logs/certify_all.log
done
echo "== certify_odd.py (1,2): extra machine check of Theorem 9.1(a)"
nice python3 certify_odd.py 1 2 160 > logs/odd_1_2.log 2>&1; grep RESULT logs/odd_1_2.log
mkdir -p forms && mv -f forms_*_*.txt forms/ 2>/dev/null
echo "certificates verified: $(grep -c VERIFIED logs/certify_all.log) / $(echo $pairs | wc -w)"
