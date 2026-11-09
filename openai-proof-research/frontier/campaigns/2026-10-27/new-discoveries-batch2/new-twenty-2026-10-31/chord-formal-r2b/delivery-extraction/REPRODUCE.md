# Reproduction

Use the fixed Lean 4.34.1 binaries and read-only pinned mathlib packages specified in `scripts/env.sh`. All paths written by the wrappers are under their own extraction root. Every Lean, leanchecker and Python call must go through `scripts/capped.sh`: two CPUs, CPU 120 s, wall 140 s, summed session RSS watchdog at 6 GiB, MALLOC_ARENA_MAX=2, lane-local TMPDIR and caches. Every Lean invocation includes -j1 -M3500 -DwarningAsError=true. Run only one heavy process at a time.

`bash scripts/rebuild.sh` serially builds every module in `modules.txt` and runs leanchecker with its explicit module name. Each successful source digest is recorded for resumption. Reuse markers only for immutable sources; invalidate dependent modules after any source change. A source archive extraction has no build products or markers.

To regenerate certificates, run `scripts/capped.sh python3 -I scripts/generate.py`, then `scripts/capped.sh python3 -I scripts/generate4.py`, then `scripts/capped.sh python3 -I scripts/generate3.py`. Python output is a certificate proposal only; all mathematical checks and exhaustive coverage are proved by the generated Lean modules.

Run `scripts/capped.sh python3 -I scripts/regression.py` for the independent small-size regression and negative controls inherited from the frozen packet. This is numerical evidence only.

For the full build and audit including its explicit-module leanchecker, run `bash scripts/validate.sh`. After a full build, use `source scripts/env.sh`, then `scripts/capped.sh "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true src/ChordComb2Audit.lean`. The audit imports the endpoint closure, includes generated declarations, reads opaque values, rejects forbidden LOCAL metadata and unapproved transitive axioms, and checks exact equality between imported declaration inventories and audited declarations. LOCAL and upstream metadata are reported separately.

`package.py` creates a source-only zip with relative paths, checks extraction safety, and extracts into a new empty lane-local `fresh-extraction`. Its extracted rebuild is the authoritative replay. No acceptance is asserted by a successful build.
