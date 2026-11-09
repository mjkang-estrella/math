All Python helper executions used the fixed guard, without limit increases:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 -B /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-mathdb-primary-qualified-breadth-r396/verify.py
```

The guard remains 512 MiB AS and sampled process-group RSS, 210 CPU seconds, 230 wall seconds. verify.py is separate from construction and exits nonzero on mismatch. It writes only this lane's final-receipt.json after successful assertions. It rechecks actual original files, root intake manifest and bindings read-only, all twenty original corpus chunks, fifty canonical records and statement hashes, exact assignment and disjointness, and exact lane payload membership plus hashes. No scientific proof certificate exists or is claimed. Initial helper failures and their corrections are retained; no resource cap was hit.

Manifest excludes exactly manifest.json and final-receipt.json. Re-run only the verifier for an existing sealed payload; modifying any payload or upstream reference makes it fail. No receipt from another lane is rewritten.
