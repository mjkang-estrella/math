#!/bin/bash
# For b >= 4: n = (a-1)(b-2) should be SAT (lower-bound witness), n = 1+(a-1)(b-2) should be UNSAT (Conjecture 4.16).
# b = 3 controls: compare with Table 11 column b = 3 and show the formula (= a) fails for even a.
D="$(cd "$(dirname "$0")" && pwd)"
for cell in "$@"; do a=${cell%,*}; b=${cell#*,}
  N=$((1+(a-1)*(b-2))); "$D/sat_cell.sh" $a $b $((N-1)); "$D/sat_cell.sh" $a $b $N
done
