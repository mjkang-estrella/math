#!/bin/bash
set -eu
cd "$(dirname "$0")/dev"
while IFS= read -r m; do
 python ../run.py -o "$m.olean" "$m.lean" > "../logs/$m-reduced01.log" 2>&1 || { cat "../logs/$m-reduced01.log"; exit 1; }
 printf '%s\n' "$m" >> ../completed-reduced-modules.txt
done < ../reduced-plan.txt
