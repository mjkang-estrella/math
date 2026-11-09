#!/bin/bash
# Sequential capped chunks (one process at a time) for m=5, n=7, all 65536 functions g.
cd "$(dirname "$0")/.."
for lo in $(seq 1000 1800 65535); do
  hi=$((lo+1800))
  python3 -I scripts/cap.py gjpo-m5-n7-$lo python3 -I scripts/gjpo.py search 5 7 $lo $hi outputs/gjpo-m5-n7-$lo.json > /dev/null
done
echo LOOPDONE
