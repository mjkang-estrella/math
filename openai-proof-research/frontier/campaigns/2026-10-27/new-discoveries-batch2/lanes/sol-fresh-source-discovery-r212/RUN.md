# Capped replay

From the repository root, run:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-fresh-source-discovery-r212/verify.py
```

The verifier checks the complete manifest, original/copy scientific hashes and compact external immutable historical references, re-extracts both PDFs to memory and exactly replays checks.py stdout/stderr. It writes only the explicitly excluded verification-receipt.json. AS and sampled process-group RSS512MiB; CPU210s; wall230s. No raised limits. Unsampled RSS transients are not excluded by the inherited40ms sampler. checks.py can be run instead of verify.py under the same command prefix for diagnostics only. Do not rerun work.py init: it is retained for workflow provenance, not replay.
