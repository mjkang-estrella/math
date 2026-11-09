#!/bin/bash
# usage: rowmotion_batch.sh OUTFILE < lines "mode a b l"; runs each with 2 parallel workers, per-job caps.
OUT=$1
xargs -P 2 -L 1 bash -c 'ulimit -t 120; ulimit -v 8000000; r=$(timeout 135 node --max-old-space-size=4096 scripts/rowmotion.js "$0" "$1" "$2" "$3" 2>&1 | tail -1 | cut -c1-400); echo "{\"job\":\"$0 $1 $2 $3\",\"result\":$( [[ $r == \{* ]] && echo "$r" || echo "\"FAILED: ${r//\"/}\"" )}"' >> "$OUT"
