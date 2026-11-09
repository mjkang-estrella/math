#!/bin/bash
# Smallest n <= 7 with no good colouring, by exhaustive enumeration (tmp/brute), for 3 <= a,b <= 8.
D="$(cd "$(dirname "$0")/.." && pwd)"
for a in 3 4 5 6 7 8; do for b in 3 4 5 6 7 8; do
  r=">7"
  for n in 2 3 4 5 6 7; do
    out=$("$D/tmp/brute" $a $b $n); g=$(echo "$out" | sed 's/.*GOOD \([0-9]*\).*/\1/')
    if [ "$g" = "0" ]; then r=$n; echo "$out"; break; fi
  done
  echo "CELL a=$a b=$b Rcyc=$r"
done; done
