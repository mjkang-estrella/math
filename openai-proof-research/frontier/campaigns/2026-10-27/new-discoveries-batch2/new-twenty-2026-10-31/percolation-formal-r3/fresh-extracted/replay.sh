#!/bin/bash
set -eu
root=$(cd "$(dirname "$0")" && pwd)
cd "$root"
mkdir -p build logs tmp
export LEAN_PATH="$root/build"
sig=$(sha256sum src/*.lean | sha256sum | cut -d' ' -f1)
while read -r m; do
 test -n "$m" || continue
 case "$m" in *[!a-zA-Z0-9_]*) exit 2;; esac
 if test "${RESUME:-0}" = 1 && test -f "logs/$m.ok" && test -f "build/$m.olean" && test "$(cat "logs/$m.ok")" = "$sig"; then continue; fi
 bash ./guard.sh "build-$m" lean -M3500 -DwarningAsError=true -o "build/$m.olean" "src/$m.lean"
 bash ./guard.sh "check-$m" leanchecker "$m"
 printf '%s\n' "$sig" > "logs/$m.ok"
done < module-order.txt
