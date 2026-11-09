#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build logs tmp
mods=(Base Bridges CountBase)
for f in src/S[0-9][0-9].lean src/T[0-9][0-9].lean; do mods+=("$(basename "$f" .lean)"); done
mods+=(Counts Controls Endpoint Audit)
for m in "${mods[@]}"; do
 if [ "${RESUME:-0}" != 1 ] || [ ! -f "logs/$m.strict.ok" ]; then
  ./capped.sh lean -M3500 -DwarningAsError=true -o "build/$m.olean" "src/$m.lean" > "logs/$m.strict.log" 2>&1
  ./capped.sh leanchecker "$m" > "logs/$m.checker.log" 2>&1
  touch "logs/$m.strict.ok"
 fi
 echo "$m replay OK"
done
if rg -n '\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern)\b|_unsafe_rec' src --glob '*.lean' --glob '!Audit.lean' > logs/source-scan.log; then
 echo 'Forbidden source token found'; exit 1
fi
echo 'Strict replay and source scan completed'
