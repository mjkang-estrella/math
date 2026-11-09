# Reproduce round 3

Run from the lane. No network or package writes are needed. All paths below stay under this lane. Lean 4.34.1 and pinned read-only mathlib packages are selected in scripts/env.sh.

```
mkdir replay-new
unzip -q source.zip -d replay-new
cd replay-new
scripts/replay3.sh
```

Use a new empty extraction directory for a fresh replay. RESUME=1 scripts/replay3.sh resumes a replay stopped between successfully checked modules; after editing an earlier dependency, use a fresh extraction instead. Checks are serial: each module is built with -j1 -M3500 -DwarningAsError=true, then leanchecker is invoked with that explicit module name. The inherited lean wrapper also supplies -j1 -M3500 to subprocess calls. Every Lean, checker and Python invocation is wrapped by scripts/capped.sh, with a process-group RSS watchdog at 6 GiB, taskset CPUs 0 and 1, CPU 120 seconds, wall 140 seconds, and MALLOC_ARENA_MAX=2. Temporary directories and caches are extraction-local. Logs have unique names. The watchdog is reaped before the wrapper returns.

The final audit uses allowOpaque=true, traverses types and values, generated declarations, inductive constructors, declaration groups and _unsafe_rec companions, and verifies closure membership. The TSV records unsafe, partial, implemented_by and extern metadata. scripts/report3.py verifies permitted axioms, local metadata, duplicate-free audited declarations, and all inherited hashes, then writes results.json. Upstream executable metadata is reported separately; it is not claimed absent. The inherited Python regression runs 42 parameter cases and negative controls for duplicate labels, the l-colour claim and odd t. The six inherited literal graph certificates are rebuilt and checked.

source.zip contains only source, documentation, manifests and replay scripts, without build files or caches. The delivered fresh run is in replay-fresh/. Its results.json is copied to the lane root. The archive hash is in source.zip.sha256. No endpoint is accepted by this replay: construction and bridge Props remain explicit.
