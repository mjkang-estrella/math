#!/bin/bash
# run_all.sh — reproducible end-to-end pipeline for the single-exceptional-digit
# family decisions. Every python invocation is memory-capped at ~3 GB (ulimit -v).
# Total runtime ~5 min (enums are checkpointed and skipped when complete).
set -e
cd "$(dirname "$0")"
CAP="ulimit -v 3000000;"

echo "=== 1. direct enumeration of 7-smooth members, L <= 3000 (checkpointed) ==="
for d in 1 2 3 4 5 6 7 8 9; do
  bash -c "$CAP timeout 900 python3 -I enum_members.py --delta $d" | tail -1
done

echo "=== 2. cascade stages 0-2 + pinning checks, per delta ==="
for d in 1 2 3 4 5 6 7 8 9; do
  bash -c "$CAP timeout 1150 python3 -I glm2.py --delta $d"
done

echo "=== 3. independent certificates ==="
bash -c "$CAP timeout 900 python3 -I verify_members.py"
bash -c "$CAP timeout 900 python3 -I delta5_certificate.py"
bash -c "$CAP timeout 300 python3 -I -c \"import sys; sys.path.insert(0,'.'); from glm2 import _assert_constants; _assert_constants(); print('constants OK')\""

echo "=== 4. Fonga/Vunga t_max validation (23 multisets vs brute force) ==="
bash -c "$CAP timeout 600 python3 -I vunga.py" | tail -1

echo "ALL DONE"
