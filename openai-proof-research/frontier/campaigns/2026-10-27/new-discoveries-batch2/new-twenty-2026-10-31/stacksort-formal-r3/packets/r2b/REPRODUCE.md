# Reproduction

Pinned Lean: /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
version 4.34.1. Read-only mathlib packages are at
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages,
with mathlib pinned to d13f23b723b8a846827a245b89c10fc7d3f11612.

Extract stacksort-seeds2-source.zip into a new empty directory INSIDE this lane,
change to that directory, and run `bash scripts/build.sh`. The script compiles
all eleven frozen modules and all new modules serially, with lean -j1 -M3500
-DwarningAsError=true, exports declaration metadata, checks exact endpoint import
closure coverage, and runs leanchecker with an explicit module argument on each
module. It retains full logs with unique timestamps. See results.json for actual
replay status; commands here are not evidence that a run succeeded.

`scripts/run.sh` is mandatory for every Lean, leanchecker and Python call.
It sets lane/extraction-local TMPDIR and XDG_CACHE_HOME, MALLOC_ARENA_MAX=2,
LEAN_NUM_THREADS=1, two CPU affinity, CPU 120 seconds, wall 140 seconds, and a
6 GiB aggregate descendant RSS watchdog with group-wide termination. Processes
run one at a time. The watchdog is joined or terminated before each wrapper exits.
Core dumps are disabled. Do not probe leanchecker options or omit its module.

The Python generators are untrusted diagnostics. To regenerate data run,
serially, `scripts/run.sh python3 -I scripts/generate.py`, then
`scripts/run.sh python3 -I scripts/split_rows.py`, and
`bash scripts/make_checked.sh`. The first script checks the top-max seeds against
the read-only cached exact table and independently enumerates literal permutations
through n=8. Generator agreement does not prove AdditiveRecursion.

The audit uses allowOpaque := true and records generated declarations, logical
dependencies, safety and partial flags, implementation and external metadata.
Its independent Python verifier reconstructs the full import graph rooted at
StackSortSeeds2Final, equates the module constant-name set with the audited set,
and traverses the endpoint dependencies. Only propext, Classical.choice and
Quot.sound are permitted. LOCAL and upstream metadata are reported separately;
upstream compiler implementation declarations are not treated as local proofs.

The numerical reductions were split by the first tuple index after an initial
whole-row-11 reduction reached Lean's -M3500 interpreter limit. No RSS-cap breach
is reported by the watchdog. The initial recursive syntax for sections generated
an unwanted compiler companion, detected by the audit and replaced by Nat.rec.
Failed logs are retained; they are not counted as successful validation.

After successful replay the script writes a new results.json for that extraction.
The source archive excludes run-dependent results and audit-summary files; the
provided lane results.json and audit-summary.json are separate validation artifacts.
This keeps the exact source archive fixed throughout its fresh extracted replay.
