#!/usr/bin/env bash
set -eu
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
for mod in BesselRatio BesselAnalytic BesselInterfaces BesselEndpoints BesselSeriesODE BesselODE BesselClosed; do
  python3 run.py -o "$mod.olean" "$mod.lean" > "$mod.log" 2>&1
done
python3 run.py Audit.lean > audit.log 2>&1
