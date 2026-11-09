# Round 5 reproduction

Use Lean 4.34.1 and the read-only mathlib package directory pinned in TASK.txt.
The bound round-4 zip has SHA-256
384a9c6a9a4e28e0e922f6545c1516216578fb8f4c73d5e469d157fddc2e378d.

Extract grid-formal-r5-source.zip into a NEW empty directory within this lane.
Run `bash scripts/replay.sh`, then `scripts/run.sh python3 scripts/report5.py`.
The script builds strictly and serially, checks each explicit module with
leanchecker, runs the complete Audit5 inventory/closure audit, and requires
all four inherited negative controls to fail. Resume markers bind source
hashes. Use a new extraction after editing any source dependency.

Every Lean, leanchecker and Python invocation goes through scripts/run.sh:
6 GiB process-group RSS watchdog, taskset CPUs 30,31, CPU 120 seconds, wall
140 seconds, MALLOC_ARENA_MAX=2, lane-local TMPDIR and caches. Lean and checker
receive -j1 -M3500 -DwarningAsError=true. No heavy processes run concurrently.
The source packet contains no build products. All logs are retained separately.
