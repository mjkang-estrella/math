#!/bin/bash
set -eu
cd "$(dirname "$0")/dev"
while IFS= read -r m; do
 python ../run.py -o "$m.olean" "$m.lean" > "../logs/$m-rebatched01.log" 2>&1 || { cat "../logs/$m-rebatched01.log"; exit 1; }
 printf '%s\n' "$m" >> ../completed-rebatched-modules.txt
done < ../rebatched-plan.txt
