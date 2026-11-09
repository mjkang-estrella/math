# Reproduction

Use Lean 4.34.1 and the read-only mathlib packages at the pin in scripts/env.sh. Every Lean, leanchecker or Python process must run through scripts/capped.sh. It enforces the 6 GiB summed session RSS watchdog, CPUs 0 and 1, CPU 120 s, wall 140 s, MALLOC_ARENA_MAX=2, and lane-local TMPDIR and caches. Lean calls use -j1 -M3500 -DwarningAsError=true. Only one heavy process runs at once.

Run bash scripts/validate.sh to build and leancheck every module in modules.txt, in strict serial order. The checker always receives an explicit module argument. The source-only archive has no build products or success markers. Resume markers are source digests; when changing a module, invalidate it and its dependents.

Run scripts/capped.sh python3 -I scripts/regression.py for independently implemented representative states and transfer tests, and small negative controls. These computations are numerical evidence only. The unconditional n=4 uniqueness negative control is inherited in ChordComb2Final and replayed as part of the build.

ChordComb4Audit imports the final endpoint. Its exact-closure inventory includes generated declarations and examines opaque values. It rejects forbidden LOCAL metadata and transitive axioms, and writes audit.jsonl. LOCAL and upstream metadata must be reported separately. The audit module itself is also compiled and leanchecked.

bash scripts/package.sh creates the source-only ZIP. All paths are relative. Extract only to a new empty directory under this lane, then run its scripts/validate.sh. The delivery logs and results.json record the actual replay status. No acceptance follows from successful validation.
