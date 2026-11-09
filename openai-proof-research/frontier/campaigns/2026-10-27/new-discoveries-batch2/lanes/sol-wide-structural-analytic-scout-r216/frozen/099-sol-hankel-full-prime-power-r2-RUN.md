# Reproduce bounded controls and final verification

From the repository workspace root, run commands separately:

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-hankel-full-prime-power-r2/checks.py
```

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-hankel-full-prime-power-r2/verify_final.py
```

The first command rewrites the timestamped check receipt, so it would intentionally invalidate the frozen final manifest unless regenerated. The second is the actual separate final verification and writes only the excluded verification-receipt.json. Do not rerun checks in a frozen packet as though its manifest were unchanged.

The guard enforces AS512MiB, sampled group RSS512MiB, CPU210s, wall230s; no raised limits or parallel numerical libraries. Sampling cannot exclude unsampled transient RSS spikes. No Lean build, browser or manuscript tool is needed.
