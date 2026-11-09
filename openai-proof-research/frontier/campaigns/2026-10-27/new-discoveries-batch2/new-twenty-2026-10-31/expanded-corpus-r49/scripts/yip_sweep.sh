#!/bin/bash
# two worker lanes (1 CPU each), alternate cases from case list; each case CPU-capped
cd "$(dirname "$0")/.."
lane=$1
awk -v L=$lane 'NR%2==L' logs/yip-case-list.txt | while read p m q; do
  timeout 2400 python3 -I scripts/yip_fast.py $p,$m 2300 >> logs/yip-sweep-lane$lane.jsonl 2>&1 || echo "{\"case\":[$p,$m],\"exit\":$?}" >> logs/yip-sweep-lane$lane.jsonl
done
