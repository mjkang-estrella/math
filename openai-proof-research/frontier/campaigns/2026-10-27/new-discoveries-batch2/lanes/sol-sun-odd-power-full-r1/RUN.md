# Capped replay

Run from /home/mj-kang/Documents/Dev/math:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-sun-odd-power-full-r1/checks/checks.py
```

Use the same prefix with checks/verify_final.py for manifest and original/copy verification. Replaying checks rewrites timestamped checks/results.json, so it invalidates the finalized manifest until deliberately regenerated. The delivered receipt verifies the delivered snapshot. Manifest excludes manifest.json and verification-receipt.json explicitly.

The same capped prefix also runs checks/pivot_deformations.py (both deformations and symbolic uniform table bounds).
