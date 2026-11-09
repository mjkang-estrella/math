# Reproduction

Run every command from this lane directory. Use the prescribed guard and environment, and do not raise the
caps:

    G=../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
    export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
    python3 -B $G python3 -B work/exact_checks.py      # exact checks C0–C4 (assertions)
    python3 -B $G python3 -B work/selftest.py          # checker vs source all-even sets
    python3 -B $G python3 -B work/sphere_exhaust.py P13_control   # positive control
    python3 -B $G python3 -B work/sphere_exhaust.py rings_13_5_4  # largest spherical universe (2^22)
    python3 -B $G python3 -B work/finalize.py          # writes manifest.json (after all other writes)
    python3 -B $G python3 -B work/verify.py            # separate verification -> verification-receipt.json

Captured outputs are in `runs/`. Each `*.out` file has a matching `*.guard` file containing the guard JSON.
Float-mode searches (`orbits`, `sphere_exhaust`, `latconv`, `ls`) are exploration and support only.
