#!/usr/bin/env bash
set -eu
ROOT=$(cd -- "$(dirname -- "$0")" && pwd)
cd "$ROOT"
mkdir -p build logs tmp
export LEAN_PATH="$ROOT/build"
signature=$(sha256sum src/*.lean | sha256sum | cut -d' ' -f1)
while IFS= read -r module; do
  [ -n "$module" ] || continue
  case "$module" in *[!a-zA-Z0-9_]*) echo 'Invalid module name' >&2; exit 2;; esac
  if [ "${RESUME:-0}" = 1 ] && [ -f "logs/$module.ok" ] && [ "$(cat "logs/$module.ok")" = "$signature" ] && [ -f "build/$module.olean" ]; then
    echo "Resuming past verified $module"
    continue
  fi
  echo "Strict replay $module"
  /usr/bin/time -f 'wall_seconds=%e peak_rss_kib=%M' -o "logs/$module.time" ./guard.sh lean -M3500 -DwarningAsError=true -o "build/$module.olean" "src/$module.lean" > "logs/$module.lean.log" 2>&1
  /usr/bin/time -f 'wall_seconds=%e peak_rss_kib=%M' -o "logs/$module.check.time" ./guard.sh leanchecker "$module" > "logs/$module.check.log" 2>&1
  printf '%s\n' "$signature" > "logs/$module.ok"
done < module-order.txt
./guard.sh python3 -I "$ROOT/scan.py" "$ROOT" > logs/source-scan.json
