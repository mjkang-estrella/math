# Capped checks

From repository root, run either command exactly with the existing unchanged guard:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-hankel-breadth-depth-r1/checks.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-hankel-breadth-depth-r1/verify_final.py
```

Limits remain AS/group sampled RSS512MiB,CPU210s,wall230s. Sampling cannot exclude unsampled RSS transients. No third-party Python packages needed; PDF verification uses pdftotext. checks.py writes deterministic check-results.json. verify_final.py writes only the explicitly excluded verification-receipt.json. The verifier checks the final artifact manifest and original/copy sources, not a full mathematical conjecture or novelty claim.
