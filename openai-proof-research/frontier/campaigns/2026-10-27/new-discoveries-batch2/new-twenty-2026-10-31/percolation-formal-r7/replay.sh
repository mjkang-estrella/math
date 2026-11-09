#!/bin/bash
set -eu
R=$(cd "$(dirname "$0")" && pwd)
cd "$R"
mkdir -p build logs tmp cache
export LEAN_PATH="$R/build"
sig=r7-v1; start=$SECONDS; donecount=0
while read -r m; do
 [[ "$m" =~ ^[A-Za-z0-9_]+$ ]] || exit 2
 sig=$(printf '%s\n%s\n' "$sig" "$(sha256sum "src/$m.lean" | cut -d' ' -f1)" | sha256sum | cut -d' ' -f1)
 if test "${RESUME:-0}" = 1 && test -f "logs/$m.ok" && test -f "build/$m.olean" && test "$(cat "logs/$m.ok")" = "$sig $(sha256sum "build/$m.olean" | cut -d' ' -f1)"; then donecount=$((donecount+1)); continue; fi
 if test "${BUDGET:-0}" -gt 0 && test "$((SECONDS-start))" -ge "$BUDGET"; then echo "Budget stop before $m"; exit 0; fi
 echo "Starting $m"
 bash ./guard.sh "build-$m" lean -M3500 -DwarningAsError=true -o "build/$m.olean" "src/$m.lean"
 bash ./guard.sh "check-$m" leanchecker "$m"
 printf '%s %s\n' "$sig" "$(sha256sum "build/$m.olean" | cut -d' ' -f1)" > "logs/$m.ok"
 donecount=$((donecount+1))
 printf '{"completed_modules":%s,"last_module":"%s"}\n' "$donecount" "$m" > progress.json
done < module-order.txt
echo "Completed $donecount modules"
