#!/bin/bash
# n=7, all y = 1 (k=0): residues r mod 16 not covered by the residue-0-mod-8 chunk; one capped process at a time.
cd "$(dirname "$0")/.."
for r in 1 2 3 4 5 6 7 9 10 11 12 13 14 15; do
  python3 -I scripts/cap.py shrinkx7k0-c${r}of16 python3 -I scripts/shrink_exhaustive.py 7 outputs/shrink-n7-k0-c${r}of16.json 7 0 $r 16 C1,C1C2,C1C2C3,S1 > /dev/null
done
echo LOOPDONE
