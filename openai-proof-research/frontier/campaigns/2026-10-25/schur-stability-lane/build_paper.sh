#!/usr/bin/env bash
set -euo pipefail
lane=$(cd -- "$(dirname -- "$0")" && pwd)
tectonic_bin="${TECTONIC:-tectonic}"
if ! command -v "$tectonic_bin" >/dev/null 2>&1; then
  tectonic_bin="$lane/../bernstein-shape-lane/tools/tectonic"
fi
export XDG_CACHE_HOME="$lane/build/cache"
mkdir -p "$lane/build" "$lane/paper/rendered"
"$tectonic_bin" --only-cached --untrusted --keep-logs "$lane/paper/main.tex" > "$lane/build/paper-build.log" 2>&1
pdftoppm -scale-to 1400 -png "$lane/paper/main.pdf" "$lane/paper/rendered/page"
pdfinfo "$lane/paper/main.pdf" > "$lane/build/paper-info.txt"
