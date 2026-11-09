# Capped local replay

Run from this lane. Do not rerun retrieval scripts on parked/denied routes.

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python verify.py
```

verify.py independently checks manifest inventory, all scientific originals and frozen copies, then replays checks.py and intervals.py as children within the same guarded group and checks deterministic output hashes. It writes verification-receipt.json, excluded from the manifest. Limits are fixed512MiB AS/groupRSS,CPU210s,wall230s,threads1, with no cap raises. finalize.py writes the manifest; verification is a separate invocation after all writes. The manifest excludes only itself and the receipt. Scientific non-resolution and missing TMNA4.10 body remain explicit even when integrity verification passes.
