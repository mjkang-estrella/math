# Exact runnable checks

All helper invocations use this fixed guard and environment, with unchanged address-space/group-RSS512MiB, CPU210s, wall230s limits:

```bash
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
G=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-quantile-aggregation-full-r1
python "$G" python "$L/verify_math.py"
python "$G" python "$L/verify_integrity.py"
```

verify_math.py is exact, standard-library only. It checks the certificate and writes math-verification.json. certificate.py uses numpy/scipy to regenerate a feasible certificate but is unnecessary for mathematical replay; search.py is the seeded diagnostic. Neither retrieval nor source refreezing is required for replay. Do not rerun retrieval against any denied route. freeze.py is historical initialization and must not replace the frozen evidence on replay.

Manifest excludes itself and verification-receipt.json. Final integrity verification is a separate guarded process after manifest writing. Re-running math verification writes identical JSON bytes; any substantive file changes require manifest regeneration and a fresh separate integrity check.
