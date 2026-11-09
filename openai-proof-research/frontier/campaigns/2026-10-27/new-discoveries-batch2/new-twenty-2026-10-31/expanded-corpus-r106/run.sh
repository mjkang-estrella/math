#!/bin/bash
set -eu
cd -- "$(dirname -- "$0")"
export TMPDIR="$PWD/tmp"
export PYTHONDONTWRITEBYTECODE=1
mkdir -p tmp logs outputs
LEANC=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanc
for name in permutation-one forest forest8 golay100 golay100_deep; do
  python scripts/limited.py "recompile-$name" "$LEANC" -O3 "scripts/$name.c" -lm -o "scripts/$name"
done
for p in 0 1 2 3; do python scripts/limited.py "permutation15-$p" scripts/permutation-one 15 "$p"; done
python scripts/limited.py forest scripts/forest
for shard in 0 1 2 3 4 5 6 7; do python scripts/limited.py "forest8-$shard" scripts/forest8 "$shard"; done
for name in primepowers100m antipodal dihedral mixed_groups group_products gonality three_minimal design_parameters drawings four_candidates split split_validate split_petersen split_strict; do
  python scripts/limited.py "replay-$name" python "scripts/$name.py"
done
python scripts/limited.py replay-golay-small python scripts/golay.py
python scripts/limited.py replay-golay100 scripts/golay100 200 100000
python scripts/limited.py replay-golay100-deep scripts/golay100_deep 500 1000000
python scripts/limited.py validate python scripts/validate.py
python scripts/report.py
