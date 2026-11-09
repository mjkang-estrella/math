# Round 4 reproduction

The source packet binds the frozen round-3 zip SHA-256
42498b10fb28faf228a1ac4ba7a509dbcd850c38caa47b03f359c2c566fa2030.
All 23 inherited sources match frozen-before.sha256 and frozen-after.sha256.

Extract grid-formal-r4-source.zip into a NEW empty directory inside this lane.
From that directory run `bash scripts/replay.sh`, then run
`scripts/run.sh python3 scripts/report4.py`. The replay is serial and resumable:
a module is marked successful only after its strict compile and explicit-module
leanchecker call pass. It retains timestamped full logs, runs Audit4 and all
negative controls. Before resetting a dependency or changing sources, use a
fresh empty extraction, rather than reusing downstream success markers.

The runner enforces 2 CPUs, CPU 120 s, wall 140 s and a 6 GiB process-group
RSS watchdog per Lean/checker/Python call. It exports MALLOC_ARENA_MAX=2,
lane-local TMPDIR and caches. Every Lean and checker call receives -j1,
-M3500 and -DwarningAsError=true. LEAN_SYSROOT and LEAN_NUM_THREADS are explicit.
The pinned package directory and Lean installation are read-only inputs.
The one local Attribute.olean compatibility build is inherited from Round 3.
There is no network step and no background work is required.
