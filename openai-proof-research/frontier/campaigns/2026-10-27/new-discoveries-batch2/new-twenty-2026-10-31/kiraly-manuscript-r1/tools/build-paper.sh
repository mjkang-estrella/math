#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")/.."
: "${TECTONIC:=tectonic}"
export OMP_NUM_THREADS=2
mkdir -p logs render
"$TECTONIC" --keep-logs paper/manuscript.tex > logs/latex-build-final.log 2>&1
pdfinfo paper/manuscript.pdf > logs/pdfinfo.log
pdftoppm -scale-to 1200 -png paper/manuscript.pdf render/page > logs/render.log 2>&1
