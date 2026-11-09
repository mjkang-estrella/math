# Replay

Run the read-only checks plus this lane's separate final receipt from the workspace root:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 -B /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-mathdb-primary-qualified-breadth-r384/verify.py
```

The guard enforces 512 MiB address space and process-group RSS, CPU 210 seconds and wall 230 seconds. The verifier changes only this lane's verification-receipt.json after every assertion passes. It never executes or mutates upstream verifiers/receipts. A mismatch exits nonzero. Add `--negative-control` to test an intentionally wrong hash after the ordinary checks; this exits 1 without writing a receipt. The original negative run is retained in negative-control.txt.

Do not rerun the acquisition/freeze/build scripts merely to verify; they document how this lane was built. `seal.py` is a build step, not a verification step. No mathematical numerical checks were performed or are represented as proofs.
