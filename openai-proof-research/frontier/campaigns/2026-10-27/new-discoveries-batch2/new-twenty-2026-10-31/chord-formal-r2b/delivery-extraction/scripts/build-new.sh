#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
source scripts/env.sh
for m in ChordComb2Base $(seq -f ChordComb2Five%g 0 62) ChordComb2Five; do
 digest=$(sha256sum "src/$m.lean" | cut -d' ' -f1)
 if [[ ! -f build/$m.ok ]] || [[ $(cat build/$m.ok) != "$digest" ]]; then
  echo "BUILD $m"
  scripts/capped.sh "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "build/$m.olean" "src/$m.lean"
  scripts/capped.sh "$LEAN_BIN/leanchecker" "$m"
  echo "$digest" > "build/$m.ok"
 fi
done
