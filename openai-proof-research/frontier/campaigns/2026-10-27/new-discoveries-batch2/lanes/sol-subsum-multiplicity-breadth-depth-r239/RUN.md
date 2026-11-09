# Reproduce under fixed guard

From /home/mj-kang/Documents/Dev/math, use:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-subsum-multiplicity-breadth-depth-r239/checks.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-subsum-multiplicity-breadth-depth-r239/verify.py
```

No network needed for these checks. helper_guard enforces512MiB address space and sampled group RSS, CPU210s, wall230s, one BLAS/OMP thread. No cap raises. checks-result.json tests exact finite controls, never the unsolved infinite theorem. verify.py validates lane manifest and original immutable science references, retrieved original bytes, and primary-to-text extraction reproducibility. Manifest excludes manifest.json and verification-receipt.json. Rebuilding documents/manifest is a separate operation using build.py and finalize.py, each under the same guard, before a fresh verify.py invocation. Do not rerun retrieval as verification.
