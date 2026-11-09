#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export SOURCE_DATE_EPOCH=1792886400
export XDG_CACHE_HOME="$PWD/build/cache"
tectonic=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/t088p133-manuscript-r2/tools/tectonic
mkdir -p output/pdf
"$tectonic" --only-cached --untrusted --keep-logs --reruns 2 --outdir output/pdf main.tex > build/paper-build.log 2>&1
if rg 'Overfull|undefined|^!' output/pdf/main.log; then
  exit 1
fi
pdfinfo output/pdf/main.pdf
