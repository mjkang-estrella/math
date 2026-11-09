# Round 5 replay

Use the exact Lean 4.34.1 binary and mathlib package roots in `scripts/env.sh` (mathlib pin d13f23b723b8a846827a245b89c10fc7d3f11612). No package is modified.

Run `bash scripts/validate.sh` from this directory. It serially compiles and leanchecks every module in dependency order. Every compiler call uses `-j1 -M3500 -DwarningAsError=true`. Every checker receives an explicit module argument. All Lean and Python commands must go through `scripts/capped.sh`: CPUs 0 and 1; CPU 120 seconds; wall 140 seconds; 6 GiB RSS watchdog; MALLOC_ARENA_MAX=2; lane-local temporary and cache directories. Do not run two drivers at once.

Replay is resumable using source SHA-256 success markers in `build`. Delete affected markers and downstream markers after any source edit; a new extraction contains no markers. `frozen/manifest.json` binds all 138 inherited source files. `scripts/merge.py` reproduces the merge from the two read-only sibling packets, verifies identical shared files, and regenerates the inherited module order; do not run it on a delivery tree after adding the new modules without regenerating the final order.

`Chord5Audit` inspects the actual final endpoint import closure with opaque values and generated declarations included, checks equality with the full module inventory, and rejects forbidden LOCAL metadata and axioms. It emits `audit5.jsonl`; upstream flags are separately reported in results.json. Audit and checker success do not imply acceptance.

The task requests `ChordFinal5.lean` but also mandates that all new modules be named `Chord5*.lean`. The endpoint module is `Chord5Final.lean` to follow the naming restriction. It explicitly retains the remaining mathematical hypotheses.

Independent numerical checks: run `scripts/capped.sh python3 -I scripts/regression.py` and `scripts/capped.sh python3 -I scripts/graph_regression.py`, sequentially. They write regression.json and graph-regression.json. The former uses a separate explicit permutation evaluator for the band erasure identities through five chords; the latter enumerates all simple graphs through six vertices. Neither is a proof of a remaining Prop.
