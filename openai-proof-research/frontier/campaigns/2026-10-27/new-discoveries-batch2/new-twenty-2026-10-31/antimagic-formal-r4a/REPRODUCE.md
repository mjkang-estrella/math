# Reproduce round 4A

Run from the lane, using a new empty lane-local extraction directory:

```
mkdir replay-new
unzip -q source.zip -d replay-new
cd replay-new
scripts/replay4a.sh
```

No network or package writes are needed. scripts/env.sh selects Lean 4.34.1 and read-only mathlib packages pinned to d13f23b723b8a846827a245b89c10fc7d3f11612. The 27-module dependency order is explicit in scripts/replay4a.sh. Each module is built with -j1 -M3500 -DwarningAsError=true, then checked by leanchecker with its explicit module argument. Every Lean, checker and Python process runs under scripts/capped.sh: a process-group RSS watchdog at 6 GiB, taskset CPUs 0 and 1, CPU 120 s, wall 140 s, and MALLOC_ARENA_MAX=2. All temporary directories, build files, logs and caches are extraction-local. The watchdog is reaped before the wrapper returns; no jobs remain at handback.

RESUME=1 scripts/replay4a.sh skips modules with successful checked markers newer than their source. Resume only an interrupted run of unchanged sources. After editing any dependency, use a fresh empty extraction: the simple marker scheme does not track transitive source changes.

The last module audits the full closure of local declarations, including generated declarations, types and opaque values, declaration groups, constructors and _unsafe_rec companions. It verifies closure membership. scripts/report4a.py verifies the permitted axiom set, all local metadata flags, uniqueness of audit rows, and inherited hashes, and writes results.json. It reports upstream metadata separately. The inherited Python checker runs 42 cases and negative controls; the inherited Lean regressions and literal finite certificates are also rebuilt and checked. These finite regressions do not prove the symbolic endpoints.

All 20 frozen inherited module hashes are in inherited-before.sha256. The replay regenerates inherited-after.sha256 and compares them. The supplied fresh run is replay-fresh/. Its logs retain every build and checker call under unique names. results.json and audit.tsv at the lane root are copied from that run. source.zip contains source, manifests, documentation and scripts only, without build outputs, caches or logs; its hash is source.zip.sha256.

The final theorem remains conditional on the two higher-depth construction Props and, for arbitrary trees, ModelBridge. Replay is validation, not acceptance.
