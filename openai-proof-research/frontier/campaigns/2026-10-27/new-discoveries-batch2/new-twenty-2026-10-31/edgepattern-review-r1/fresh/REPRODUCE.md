# Replay

Extract `edgepattern-r5-source.zip` into a new empty directory. Do not copy compiled files into it. Set:

```sh
export LEAN_BIN=/path/to/lean-4.34.1-linux/bin/lean
export LEAN_PACKAGES=/path/to/pinned/.lake/packages
python3 -I scripts/replay.py
python3 -I scripts/negative.py
python3 -I scripts/check-auditor.py
```

Lean must be 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`; mathlib is pinned at `d13f23b723b8a846827a245b89c10fc7d3f11612`. The required external package olean cache is read-only. The driver constructs LEAN_PATH from the extracted sources and that cache, removes inherited LEAN/LAKE variables, uses an empty local HOME and TMPDIR, and refuses any existing `.olean` anywhere under the extraction root.

`modules.json` orders all 268 proof-closure modules and the new audit module by local imports. Legacy audit tooling is included as immutable source, but is outside that build and the proof closure. Each Lean compilation uses `-j1 -DwarningAsError=true`; each compiled module is then checked by `leanchecker`. The watchdog sets at most two CPUs, 120 CPU seconds, 140 wall seconds, MALLOC_ARENA_MAX=2, and samples private RSS every 0.05 seconds with a 5.75 GiB kill threshold, below the requested 6 GiB cap. The same watchdog surrounds version and kernel-checker calls. Processes run sequentially.

Logs and per-call resource receipts are written to `logs/`. `replay-receipt.json` records exit codes and all source hashes. `replay-AuditR5.log` contains the expression DAG inventory, all declaration metadata and final policy totals. `replay-EndpointR5.log` contains both `#print axioms` reports.

The negative driver requires normal Lean error rejections for the positive conjecture, a swapped root label and adjacency reflection without acyclicity. It also checks refusal to replay a directory containing existing oleans. A timeout or resource kill does not count as an expected negative result.

The supplied validation receipts distinguish the full fresh proof replay from a subsequent tooling-only auditor repair. The final auditor uses an explicit Nat.rec fold to avoid Lean compiler-generated partial recursion helpers. It was rebuilt, kernel-checked, and safety-checked from a separate new empty source extraction against the hash-identical freshly checked proof-module cache. A normal full replay of the final packet builds this final auditor directly. No endpoint proof source changed after the full replay.
