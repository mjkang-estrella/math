#!/usr/bin/env bash
set -eu
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
python3 run.py -o BesselRatio.olean BesselRatio.lean > build.log 2>&1
python3 run.py -o BesselAnalytic.olean BesselAnalytic.lean > analytic.log 2>&1
python3 run.py -o BesselInterfaces.olean BesselInterfaces.lean > interfaces.log 2>&1
python3 run.py Audit.lean > audit.log 2>&1
