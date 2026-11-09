#!/bin/bash
set -eu
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
for mod in Source Algebra Recurrence Automaton Enumeration Suffix; do
  python lean_guard.py "$mod.log" -o "$mod.olean" "$mod.lean"
done
python lean_guard.py Audit.log Audit.lean
