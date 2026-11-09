#!/bin/bash
set -eu
cd "$(dirname "$0")/extracted-source/formal"
while IFS= read -r m; do
 python ../run.py -o "$m.olean" "$m.lean" > "../fresh-logs/$m.log" 2>&1 || { cat "../fresh-logs/$m.log"; exit 1; }
 printf '%s\n' "$m" >> ../fresh-completed.txt
done < ../fresh-plan.txt
