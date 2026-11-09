# Reproduction

Use Lean 4.34.1 and the read-only mathlib package cache pinned to
d13f23b723b8a846827a245b89c10fc7d3f11612, at the absolute paths in scripts/lean.sh.

Extract grid-formal-r3-source.zip into a new empty directory under this lane.
Run bash scripts/replay.sh from the extraction. The script builds a read-only
symlink overlay of the upstream cache, recompiles the one missing cache module
locally, then compiles and leanchecks all 23 modules serially. It is resumable:
per-module source hashes and completion markers are stored in build/.
Use a new build directory after changing dependencies.

Every Lean/leanchecker invocation goes through scripts/lean.sh and scripts/run.sh:
two CPUs (0,1), CPU 120 s, wall 140 s, RSS watchdog 6 GiB for the process group,
MALLOC_ARENA_MAX=2, -j1 -M3500, warningAsError, lane-local TMPDIR and cache.
Every Python utility must be invoked through scripts/run.sh as well.
leanchecker is always given one explicit module name.

Audit3 inventories the complete endpoint import closure, including generated
declarations and opaque bodies, checks inventory/audited set equality in both
directions, rejects forbidden LOCAL metadata and transitive axioms, and writes
audit.jsonl. Summarize with scripts/run.sh python3 scripts/report.py.
The two inherited auditors are frozen and retained; Audit3 is the current audit.

The development generators are retained for provenance; replay uses the checked
Lean sources directly and does not regenerate them.
