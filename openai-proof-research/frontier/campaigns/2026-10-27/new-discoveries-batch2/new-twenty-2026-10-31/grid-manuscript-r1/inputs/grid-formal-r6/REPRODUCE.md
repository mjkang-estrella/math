# Round 6 reproduction

Use Lean 4.34.1 at the exact binary path in TASK.txt, and the read-only mathlib
package tree at revision d13f23b723b8a846827a245b89c10fc7d3f11612.
Extract grid-formal-r6-source.zip into a NEW empty directory inside this lane.
Run `bash scripts/replay.sh` there, followed by
`bash scripts/run.sh python3 scripts/report6.py`.

The replay driver builds strictly and serially all 47 modules in dependency
order and runs leanchecker with an explicit module argument on every module.
It compiles the missing pinned mathlib Bound.Attribute artifact into the local
build tree. Only upstream packages are symlinked; no upstream files are changed.
It runs Audit6 and all inherited auditors and requires four negative controls
to fail. Replay markers bind individual source hashes and a full source-set
hash. A failed module resumes on rerun; after source edits use a new extraction.

Every Lean, leanchecker and Python process runs through scripts/run.sh, with
a 6 GiB process-group RSS watchdog, taskset CPUs 30,31, 120 seconds CPU and
140 seconds wall per call, MALLOC_ARENA_MAX=2, lane-local TMPDIR and caches.
Lean and leanchecker receive -j1 -M3500 -DwarningAsError=true. Only one heavy
process runs at once. Logs have unique timestamp/PID prefixes and are retained.

Audit6 includes opaque values and generated declarations; it checks the entire
imported inventory in both directions and independently the endpoint's import
closure. It rejects forbidden LOCAL flags, companions, attributes and transitive
axioms. LOCAL and upstream metadata are reported separately. Upstream unsafe
implementation infrastructure is reported, not attributed to LOCAL proofs.
The endpoint's transitive axioms are checked separately by #print axioms.
