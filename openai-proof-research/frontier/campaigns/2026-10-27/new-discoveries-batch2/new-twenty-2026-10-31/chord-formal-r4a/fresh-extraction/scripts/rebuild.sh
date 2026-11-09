#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
source scripts/env.sh
mkdir -p build logs tmp cache
while read -r m; do
 digest=$(sha256sum "src/$m.lean" | cut -d' ' -f1)
 if [[ ! -f "build/$m.ok" ]] || [[ "$(cat "build/$m.ok")" != "$digest" ]]; then
  scripts/check.sh "$m"
  echo "$digest" > "build/$m.ok"
 fi
done < modules.txt
