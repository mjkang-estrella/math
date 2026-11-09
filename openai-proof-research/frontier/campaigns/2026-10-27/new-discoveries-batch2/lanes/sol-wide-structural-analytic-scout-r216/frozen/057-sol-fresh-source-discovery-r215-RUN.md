Run from /home/mj-kang/Documents/Dev/math. Every helper, Python, retrieval, edit and hash command must use this cap; do not run scripts directly:

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-fresh-source-discovery-r215/verify.py
```

For the mathematical checker alone, replace the final verify.py with checks.py. The checker is deterministic, uses exact fractions, and only prints JSON. No network is used in verification. AS/RSS512MiB, CPU210s, wall230s; no raised caps. Original helper monitors sampled process-group RSS; unsampled transients are not ruled out. Native bounded reads/apply_patch are allowed by the assignment.

manifest.json explicitly excludes itself and verification-receipt.json. The verifier runs after all final writes and writes only its excluded receipt. Administrative snapshots are checked as files but never compared with mutable live NEXT/ledger/context. Re-running the verifier updates only the excluded receipt.
