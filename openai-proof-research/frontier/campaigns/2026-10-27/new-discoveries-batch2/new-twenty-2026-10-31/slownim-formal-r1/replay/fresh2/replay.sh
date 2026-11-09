#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build logs tmp
# One module per process, resumable only while the complete source binding agrees.
binding=$(sha256sum src/*.lean run.sh modules.txt | sha256sum | cut -d' ' -f1)
while read -r module; do
  stamp="build/$module.replayed"
  if [ -f "$stamp" ] && [ "$(cat "$stamp")" = "$binding" ]; then continue; fi
  ./run.sh lean -M3500 -DwarningAsError=true -o "build/$module.olean" "src/$module.lean" > "logs/$module.lean.log" 2>&1
  ./run.sh leanchecker "$module" > "logs/$module.leanchecker.log" 2>&1
  printf '%s\n' "$binding" > "$stamp"
done < modules.txt
if rg -n '\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool|implemented_by|partial)\b|\[extern' src --glob '*.lean' --glob '!Audit.lean' > logs/source-scan.log; then
  exit 1
fi
printf 'PASS: forbidden proof constructs absent\n' > logs/source-scan.log
sha256sum src/*.lean > logs/sources.sha256
