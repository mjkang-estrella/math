# Reproduce

Extract the source-only packet to a new empty directory. Do not reuse any `.olean` files. Set `LEAN_BIN` to the pinned Lean 4.34.1 binary (commit 5045d0056413266e57c625dcd7c365b10e377c52), and `LEAN_PACKAGES` to the read-only package cache with mathlib pinned at d13f23b723b8a846827a245b89c10fc7d3f11612. Run:

```sh
python3 -I replay.py
```

The driver rejects existing oleans, verifies the source manifest, clears the inherited environment and uses only packet-local home and temporary directories. Each Lean, checker and audit-check process has at most two CPUs, 120 CPU seconds, a 140 second wall guard, a sampled aggregate private RSS guard at 6 GiB, 64 GiB address space and MALLOC_ARENA_MAX=2. Each proof is built with `-j1 -DwarningAsError=true`; each module is checked by leanchecker. Full declaration audits use `c.type`, `c.value? true`, safety flags and transitive axioms, with lossless shared expression DAGs and an independent DAG consistency check. Every negative control must fail for its intended reason.

The trusted upstream dependencies are the pinned Lean and mathlib cache. No network access is needed. Logs and per-call receipts are written under `logs/`. `logs/replay-receipt.json` exists only after all checks pass. The two final theorems are in `FinalEndpoints` (the corrected existence theorem is defined in `FinalExistence`).

Lazy generated equation lemmas can be emitted by more than one importing module. The audit checker verifies canonical full-type and full-body hash equality for repeated names, and reports unique declarations separately from module audit occurrences.
