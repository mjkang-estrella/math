#!/usr/bin/env bash
# Copyright (c) 2026 Myeongjin Kang. MIT License.
set -euo pipefail
public_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
draft_root=$(CDPATH= cd -- "$public_dir/../.." && pwd)
export XDG_CACHE_HOME="$draft_root/build/cache"
export XDG_CONFIG_HOME="$draft_root/build/config"
export XDG_DATA_HOME="$draft_root/build/data"
export TMPDIR="$draft_root/tmp"
export PYTHONDONTWRITEBYTECODE=1
export SOURCE_DATE_EPOCH=1792454400
mkdir -p "$XDG_CACHE_HOME" "$XDG_CONFIG_HOME" "$XDG_DATA_HOME" "$TMPDIR" "$draft_root/build/tex"
tectonic_bin=${TECTONIC_BIN:-"$draft_root/tools/tectonic"}
"$tectonic_bin" --version
python3 -B "$public_dir/support/reproduce.py" "$draft_root/build/checks" > "$draft_root/build/exact-reproduction.log"
cmp "$public_dir/witness-tables.tex" "$draft_root/build/checks/witness-tables.tex"
cd "$public_dir"
"$tectonic_bin" --untrusted --keep-logs --keep-intermediates --reruns 2 --outdir "$draft_root/build/tex" main.tex > "$draft_root/build/tex/console.log" 2>&1
cp "$draft_root/build/tex/main.pdf" "$public_dir/output/pdf/main.pdf"
python3 -B "$public_dir/support/qa.py" "$draft_root"
pdftoppm -r 120 -png "$public_dir/output/pdf/main.pdf" "$public_dir/renders/page" > "$draft_root/build/render.log" 2>&1
pdfinfo "$public_dir/output/pdf/main.pdf" > "$draft_root/build/pdfinfo.txt"
pdftotext -layout "$public_dir/output/pdf/main.pdf" "$draft_root/build/main.txt"
