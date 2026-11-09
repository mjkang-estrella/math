# Reproduction

Use Lean 4.34.1 at /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin. Packages are read-only under /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages; mathlib is pinned to d13f23b723b8a846827a245b89c10fc7d3f11612.

Extract stacksort-source.zip into a new empty directory INSIDE this lane. Run `bash scripts/replay.sh` there. The ordered list scripts/order.txt is explicit and can be resumed at a failed module. Every Lean call uses -j1 -M3500 -DwarningAsError=true. Every leanchecker invocation has an explicit module argument. Each heavy process is serial, with taskset on CPUs 0,1, CPU 120 s, wall 140 s, MALLOC_ARENA_MAX=2, and a shell RSS watchdog summing the process tree and killing it at 6 GiB. Python calls use the same wrapper. TMPDIR, XDG_CACHE_HOME, logs and generated oleans are within the extracted directory.

The wrapper itself is shell, avoiding an unmonitored Python bootstrap. It waits for and terminates its watchdog before returning. No network or lake invocation is needed. The only read dependencies outside the lane are the pinned Lean distribution and package oleans.

`bash scripts/run.sh python3 -I scripts/regression.py` independently checks table arithmetic and negative controls; this is diagnostic. Kernel row proofs and G_130_eq_lower130 are the numerical certificate. `scripts/generate.py` regenerates the literal table and row modules; `scripts/linkage.py` regenerates the linkage proof.

The declaration audit uses allowOpaque=true, records all imported declarations and generated compiler symbols, and verifies exact equality with the import closure of StackSortInj2Final. The metadata of local frozen/new declarations is distinguished from upstream metadata. Audit scripts are executable verification tools; no unsafe code occurs in the mathematical modules.
