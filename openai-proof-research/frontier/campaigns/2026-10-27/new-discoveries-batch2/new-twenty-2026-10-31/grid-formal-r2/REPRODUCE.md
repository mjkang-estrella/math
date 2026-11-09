# Reproduce

In an empty extraction of grid-formal-r2-source.zip run:

    python3 scripts/replay.py

The Lean 4.34.1 binary and pinned read-only mathlib package paths are in TASK.txt.
No network or git is needed. The script resumes using replay-state.json,
rebuilds strictly serially and runs leanchecker on every module.
scripts/lean.sh enforces -j1 -M3500 -DwarningAsError=true, 2 CPUs, CPU 120 seconds,
wall 140 seconds, MALLOC_ARENA_MAX=2, lane-local temporary/cache paths and managed
RSS 6 GiB. Each invocation retains a unique full log. Nothing is detached.

A read-only symlink overlay provides pinned dependencies. The missing
Mathlib.Tactic.Bound.Attribute artifact is rebuilt locally from pinned source.
The pinned package cache is never changed.

Audit2 checks all imported declarations, including generated names, using
allowOpaque=true. Both full and endpoint-closure inventories are compared in
both directions. LOCAL metadata and transitive axioms are checked. Imported
upstream metaprogramming infrastructure has broader metadata, separately reported
in replay-report.json; it is not presented as LOCAL theorem dependencies.

The 3 inherited negative controls must fail: an incorrect equitable partition,
a free vertex in the 3×3 grid, and reversed refinement order. These do not prove
ExceptionalNoIso, which remains a premise. Both auditors are also kernel checked.
Fresh extraction evidence is under verification/.
