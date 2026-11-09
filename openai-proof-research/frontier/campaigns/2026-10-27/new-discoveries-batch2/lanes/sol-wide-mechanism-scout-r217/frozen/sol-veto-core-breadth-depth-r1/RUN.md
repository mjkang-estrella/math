# Capped replay

Run from any directory, setting L to this lane's absolute path and G to
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py.
Each command must use the exact existing guard and unchanged caps:

    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python "$G" python "$L/scalar_checks.py" --verify
    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python "$G" python "$L/verify.py"

checks.py is the finite m=3 metric-LP experiment (about6 seconds). It writes
check-results.json deterministically and explicitly sets HiGHS threads=1;
the wrapper emits an option-pass-through warning. Run it under the same guard.
It requires numpy/scipy and is not a universal proof checker. Do not rerun
retrieve.py or history.py to verify the packet: their source bodies and exact
hash references are already retained, and verify.py checks them read-only.

finalize.py freezes new retrieval bodies, generates provenance and the manifest;
it precedes the separate verify.py invocation. The manifest explicitly excludes
itself and verification-receipt.json. No admin live ledger is bound as science.
