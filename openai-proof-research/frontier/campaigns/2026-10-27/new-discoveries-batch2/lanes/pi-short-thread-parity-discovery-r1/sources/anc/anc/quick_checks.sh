#!/bin/bash
# Fast sanity checks for "Nim heaps in the Game of Cycles" (a few minutes in total).
# Requirements: python3 with networkx, g++ (C++17).   Usage:  bash quick_checks.sh
set -u
cd "$(dirname "$0")"
ROOT=$(pwd)
PASS=0; FAIL=0
check() {  # check "description" "expected substring" command...
  local desc="$1" exp="$2"; shift 2
  local out; out=$("$@" 2>&1)
  if grep -qF -- "$exp" <<< "$out"; then echo "PASS  $desc"; PASS=$((PASS+1));
  else echo "FAIL  $desc"; echo "      expected: $exp"; echo "$out" | tail -3 | sed 's/^/      got: /'; FAIL=$((FAIL+1)); fi
}
echo "== compiling C++ programs"
g++ -O2 -std=c++17 -o raw_cpp/raw raw_cpp/raw.cpp
g++ -O2 -std=c++17 -o raw_cpp/fam raw_cpp/fam.cpp
g++ -O2 -std=c++17 -o core/spiderk core/spiderk.cpp
g++ -O2 -std=c++17 -o onetwoj/fsolve onetwoj/fsolve.cpp
g++ -O2 -std=c++17 -o independent_checks/v3/pc3 independent_checks/v3/pc3.cpp

echo "== Section 7: counterexamples with the raw rules (no theory used)"
check "S(1,3,7) has Grundy value 0 (Thm 7.1)"  "markable = 11 grundy = 0" python3 core/brute.py 2 4 8
check "S(1,4,6) has Grundy value 0 (Thm 7.1)"  "markable = 11 grundy = 0" python3 core/brute.py 2 5 7
check "H(5,2|1|3,1) has value 4 (Thm 7.1c)"   "H (5, 2, 1, 3, 1) n= 17 m= 12 decomp G= 4 brute G= 4" bash -c "cd core && python3 htree.py"
check "H(3,1|3|4,1) has value 2 (Thm 7.1c)"   "H (3, 1, 3, 4, 1) n= 17 m= 12 decomp G= 2 brute G= 2" bash -c "cd core && python3 htree.py"
check "Zandee counterexample, value 4 (Prop 7.2)" "Grundy value with 7->8 marked: 4" bash -c "cd core && python3 zandee_brute.py"
check "raw C++ census, n=15: 2 counterexamples (Table 2)" "parity-conj counterexamples 2" bash -c "cd raw_cpp && python3 census.py 15"
echo "== Section 4: run values"
check "B_k = k (Thm 4.3)" "B [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10" bash -c "cd core && python3 runs.py"
echo "== Section 7.4: large Grundy values"
check "S(17,90,95) has value 32 (Thm 7.3; about 30 s)" "grundy=32" core/spiderk 18 91 96
echo "== Section 8: the family S(2,3,z)"
check "Table 6 for r<=100 and g(S(2,3,z)) (Thm 8.5, 8.1)" "ALL CHECKS PASSED" bash -c "cd families && python3 verify23.py 100 160"
echo "== Section 9: the family S(1,2j,z)"
check "Lemmas 9.3-9.7 and Thm 9.1 for y=4,6,8,10, z<=300" "bad 0" bash -c "cd onetwoj && python3 verify_lemmas.py 300 4 6 8 10"
echo "== Section 10: short threads"
check "all trees with <=16 vertices and threads <=2 obey parity (Cor 10.4)" "n=16 alltrees=19320" bash -c "independent_checks/v3/pc3 tree 2 4 16 | grep -v BADTREE"
check "  ... and none of them is bad" "OK" bash -c "if independent_checks/v3/pc3 tree 2 4 16 | grep -q BADTREE; then echo BAD; else echo OK; fi"
echo
echo "passed: $PASS   failed: $FAIL"
