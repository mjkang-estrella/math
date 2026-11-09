#!/bin/bash
set -eu
R=$(cd "$(dirname "$0")" && pwd)
cd "$R"
mkdir -p build logs tmp cache
export LEAN_PATH="$R/build"
sig=r7-v2
start=$SECONDS
count=0
closed=0
while read -r m; do
 [[ "$m" =~ ^[A-Za-z0-9_]+$ ]] || exit 2
 sig=$(printf '%s\n%s\n' "$sig" "$(sha256sum "src/$m.lean" | cut -d' ' -f1)" | sha256sum | cut -d' ' -f1)
 stamp="$sig $(test ! -f "build/$m.olean" || sha256sum "build/$m.olean" | cut -d' ' -f1)"
 if ! { test "${RESUME:-0}" = 1 && test -f "logs/$m.ok" && test -f "build/$m.olean" && test "$(cat "logs/$m.ok")" = "$stamp"; }; then
  if test "${BUDGET:-0}" -gt 0 && test "$((SECONDS-start))" -ge "$BUDGET"; then echo "Budget stop before $m"; exit 0; fi
  echo "Starting $m"
  bash ./guard.sh "build-$m" lean -M3500 -DwarningAsError=true -o "build/$m.olean" "src/$m.lean"
  bash ./guard.sh "check-$m" leanchecker "$m"
  printf '%s %s\n' "$sig" "$(sha256sum "build/$m.olean" | cut -d' ' -f1)" > "logs/$m.ok"
 fi
 count=$((count+1))
 if [[ "$m" =~ ^MaskChain[0-9]{4}$ ]]; then closed=$(((10#${m#MaskChain}+1)*100)); fi
 printf '{"completed_modules":%s,"last_module":"%s","closed_additions":%s,"remaining_additions":%s}\n' "$count" "$m" "$closed" "$((129671-closed))" > progress.json
done < module-order.txt
echo "Completed $count modules"
