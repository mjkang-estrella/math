# Exact replay

Run from any working directory; paths are absolute. All helpers remain under the fixed guard.

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-wide-new-mechanism-scout-r220/checks.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-wide-new-mechanism-scout-r220/verify.py
```

Sources and failed-search metadata are retained; work.py supports bounded arXiv retrieval, but replay does not require network retrieval. No historical inaccessible interval needs reopening. finalize.py regenerates provenance, checks output and manifest; after any regeneration, run verify.py in a separate guarded process. Manifest excludes itself and verification-receipt.json.
