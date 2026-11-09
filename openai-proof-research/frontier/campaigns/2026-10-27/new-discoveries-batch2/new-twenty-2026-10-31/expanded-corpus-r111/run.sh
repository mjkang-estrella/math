#!/usr/bin/env bash
set -euo pipefail
lane_dir=$(cd -- "$(dirname -- "$0")" && pwd)
export PYTHONDONTWRITEBYTECODE=1
export TMPDIR="$lane_dir/outputs"
for script in generate_graphs nuts_exact verify_nuts words words_extended dihedral codes homology matroids sign_orbits; do
  python "$lane_dir/scripts/cap.py" "replay-$script" python "$lane_dir/scripts/$script.py"
done
for size in 17 18 20; do
  python "$lane_dir/scripts/cap.py" "replay-orbits-$size" python "$lane_dir/scripts/orbits.py" "$size"
done
python "$lane_dir/scripts/cap.py" replay-numeric python "$lane_dir/scripts/numeric.py"
