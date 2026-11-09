# Reproduction

Run python3 scripts/replay.py from a fresh extraction of grid-formal-r1-source.zip.
All writes remain inside that extraction. The script is resumable, hashes all source
modules for invalidation, and uses unique per-call log names. Do not run two replays
at once. Dependencies are the pinned read-only packages at
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
(mathlib d13f23b723b8a846827a245b89c10fc7d3f11612) and Lean 4.34.1 at
/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin.

The cache lacks Mathlib/Tactic/Bound/Attribute.olean.private. Replay makes a
read-only symlink overlay of cache objects and recompiles that one upstream source
module in its local build tree. No dependency cache is modified.

Every compiler call uses -j1 -M3500 -DwarningAsError=true; taskset 0,1;
CPU 120 seconds, timeout 140 seconds; RSS monitor 6 GiB for the process group;
MALLOC_ARENA_MAX=2; lane-local TMPDIR/cache. Checker calls pass -j1 -M3500
(flags are accepted but checker CPU parallelism is bounded by affinity).
Leanchecker runs one named module per invocation, never the entire cache.

Dependency order: GridBasic, GridSymmetry, GridFinal, GridChecks, GridRegression,
Audit. The latter audits the complete imported declaration inventory including
generated declarations and proof bodies with allowOpaque := true, checks inventory
set equality, checks local flags and transitive axioms, and records upstream metadata
separately. Kernel ConstantInfo is used, not elaborator axiom stubs for imported proofs.
Upstream unsafe implementation metadata is reported, not mistaken for local code.
Negative controls must fail to compile. Replay-report.json summarizes the run.

The source zip contains only Lean sources, scripts and prose, with relative safe paths;
no compiled objects, symlinks, cache files or replay outputs. This is a PARTIAL handback.
