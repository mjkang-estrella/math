#!/bin/bash
set -eu
exec 9>"$(dirname "$0")/replay.lock"
flock -n 9 || exit 3
R=$(cd "$(dirname "$0")" && pwd)
cd "$R"
mkdir -p build logs
export LEAN_PATH="$R/build"
sig=r8-v1; start=$SECONDS; count=0; closed=0
while read -r m; do
 [[ "$m" =~ ^[A-Za-z0-9_]+$ ]] || exit 2
 sig=$(printf '%s\n%s\n' "$sig" "$(sha256sum "src/$m.lean" | cut -d' ' -f1)" | sha256sum | cut -d' ' -f1)
 if test "${RESUME:-0}" = 1 && test -f "logs/$m.ok" && test -f "build/$m.olean" && test "$(cat "logs/$m.ok")" = "$sig $(sha256sum "build/$m.olean" | cut -d' ' -f1)"; then count=$((count+1)); continue; fi
 if test "${BUDGET:-0}" -gt 0 && test "$((SECONDS-start))" -ge "$BUDGET"; then echo "Budget stop before $m"; exit 0; fi
 echo "Starting $m"
 bash "$R/guard.sh" "build-$m" lean -M3500 -DwarningAsError=true -o "build/$m.olean" "src/$m.lean"
 bash "$R/guard.sh" "check-$m" leanchecker "$m"
 printf '%s %s\n' "$sig" "$(sha256sum "build/$m.olean" | cut -d' ' -f1)" > "logs/$m.ok"
 count=$((count+1))
 printf '{"completed_modules":%s,"last_module":"%s","status":"fresh compile and explicit-module check passed"}\n' "$count" "$m" > "$R/progress.json"
done < module-order.txt
