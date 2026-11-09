Run from the repository root:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 -B /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-mathdb-primary-qualified-breadth-r392/verify.py
```

Guard fixed at 512MiB AS/group RSS, CPU210s, wall230s, single-threaded. No raised cap. The independent verifier writes only this lane's final-receipt.json after all assertions pass. It never invokes an upstream verifier. Do not rerun freeze.py: input-bindings.json is immutable and the freeze script rejects overwriting it. Fetch scripts are provenance of already-completed requests, not instructions to retry failed routes. No scientific computation is needed to support these zero-proposal dispositions.
