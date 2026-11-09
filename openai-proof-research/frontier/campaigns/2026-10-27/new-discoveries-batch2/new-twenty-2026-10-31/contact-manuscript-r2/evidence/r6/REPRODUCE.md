# Reproduce r6

Extract contact-r6-source.zip into a new empty directory. Run there:

```sh
export LEAN_BIN=/absolute/path/to/lean-4.34.1-linux/bin/lean
export LEAN_PACKAGES=/absolute/path/to/pinned/.lake/packages
python3 -I -B scripts/replay-r6.py
```

Lean is 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52.
The read-only mathlib package cache is pinned to
d13f23b723b8a846827a245b89c10fc7d3f11612. Dependencies use the supplied
cached compiled libraries; no dependency-source rebuild is claimed.
The driver refuses any pre-existing local olean, ilean, ir or build directory.
It scans sources for forbidden proof/evaluation tokens, copies only sources to
build/, then serially compiles all 33 modules with -j1 -DwarningAsError=true,
and runs leanchecker separately on every module. LEAN_PATH contains only the
fresh local build and the chosen package libraries. Every Lean and checker call
has a watchdog: two-CPU affinity, 120 CPU seconds, 140 wall seconds, sampled
private RSS ≤ 6 GiB, MALLOC_ARENA_MAX=2. Temporary paths stay under replay-logs.
Seventeen independently failing negative controls must return exactly 1 without
a resource kill. The final audit covers all imported local declarations,
including generated companions, full type and opaque-inclusive body as a
lossless expression DAG, safety/partial flags, and transitive axiom lists.
Only propext, Classical.choice and Quot.sound are permitted.

The delivered fresh-extraction/replay-logs contains the actual clean replay,
per-call receipts, full logs (gzip for large outputs), audit-r6.dag,
audit-inventory.json and complete.json. Failed development attempts, if any,
are separately under logs/ and do not constitute the final replay.

For the optional symbolic diagnostic (requires installed SymPy), run
python3 -I -B scripts/regression.py under scripts/capped.py with a log path.
If isolated Python cannot see an installed read-only package directory, set
REGRESSION_SITE to its absolute path. This run used the existing
/home/mj-kang/.local/lib/python3.14/site-packages directory; no installation
or dependency modification was performed. The initial missing-package error
is retained as logs/regression.log, and the successful check as
logs/regression-final.log.
The analytic argument and its explicit limits are in REGRESSION.md.

inputs/before.json and inputs/after.json bind the read-only r5, review and root
ruling inputs; inputs/ contains hash-identical copies. The final source packet
contains only Lean sources, replay scripts and documentation, never oleans.
