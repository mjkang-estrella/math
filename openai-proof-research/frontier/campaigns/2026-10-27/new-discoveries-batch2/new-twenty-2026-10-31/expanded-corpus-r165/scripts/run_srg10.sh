#!/bin/bash
L="$(cd "$(dirname "$0")/.." && pwd)"; cd "$L"
for s in 0 1000000 2000000 3000000 4000000 5000000 6000000 7000000 8000000 9000000 10000000 11000000; do
  scripts/cap.sh python3 -I scripts/srg_search.py scripts sources/graphdata/graph10c.g6.gz $s 1000000 > logs/srg-10-$s.json 2> logs/srg-10-$s.err
  echo "chunk $s rc=$?" >> logs/srg-10-progress.log
done
