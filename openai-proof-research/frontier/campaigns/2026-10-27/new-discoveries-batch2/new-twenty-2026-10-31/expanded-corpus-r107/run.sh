#!/bin/bash
set -eu
cd -- "$(dirname -- "$0")"
export PYTHONDONTWRITEBYTECODE=1
export TMPDIR="$PWD/tmp"
mkdir -p tmp logs outputs
python scripts/limited.py replay-strict python scripts/replay.py
# Diagnostics are separate and not dependencies of the formal certificate.
for mode in dickson squares digits; do python scripts/limited.py "replay-$mode" python scripts/early.py "$mode"; done
for mode in codes digraphs cyclic schur permutations digits-dual; do python scripts/limited.py "replay-$mode" python scripts/more.py "$mode"; done
for mode in partitions hurwitz; do python scripts/limited.py "replay-$mode" python scripts/numeric.py "$mode"; done
for name in repeated-code digits-ansatz cyclotomic hypergraphs trees; do python scripts/limited.py "replay-$name" python "scripts/$name.py"; done
python scripts/report.py
python scripts/validate.py
