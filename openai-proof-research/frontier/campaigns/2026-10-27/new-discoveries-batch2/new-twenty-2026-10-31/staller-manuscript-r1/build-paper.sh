#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
: "${TECTONIC:=tectonic}"
export OMP_NUM_THREADS=2
"$TECTONIC" --only-cached --keep-logs paper.tex > tex-build.log 2>&1
mkdir -p render
pdftoppm -scale-to 1400 -png paper.pdf render/page
