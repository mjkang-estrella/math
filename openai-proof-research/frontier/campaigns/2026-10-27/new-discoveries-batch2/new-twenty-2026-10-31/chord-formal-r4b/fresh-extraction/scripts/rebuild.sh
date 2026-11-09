#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
source scripts/env.sh
mkdir -p build logs tmp cache
while read -r m; do
 digest=$(sha256sum "src/$m.lean" | cut -d' ' -f1)
 if [[ ! -f build/$m.ok ]] || [[ $(cat "build/$m.ok") != "$digest" ]]; then
  echo "BUILD $m"
  scripts/capped.sh "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "build/$m.olean" "src/$m.lean"
  scripts/capped.sh "$LEAN_BIN/leanchecker" "$m"
  echo "$digest" > "build/$m.ok"
 fi
done < modules.txt
