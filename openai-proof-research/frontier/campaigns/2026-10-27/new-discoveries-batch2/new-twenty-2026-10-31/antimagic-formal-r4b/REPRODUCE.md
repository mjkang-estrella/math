# Reproduce Round 4B

From this lane, extract source.zip into a new empty directory inside the lane:

```
mkdir replay-new
unzip -q source.zip -d replay-new
cd replay-new
scripts/replay4b.sh
```

For a stopped run, `RESUME=1 scripts/replay4b.sh` skips already checked modules whose source digests match, until the first mismatch, then rebuilds that module and every later module. The final closure audit and Python regressions always rerun. Package paths and tools are fixed in scripts/env.sh. No network or writes to the read-only packages occur. Do not move the replay outside the assigned lane.

Every Lean, leanchecker and Python process is launched through scripts/capped.sh. The wrapper uses two CPUs (0,1), CPU 120 seconds, wall 140 seconds, a process-group RSS watchdog at 6 GiB, and MALLOC_ARENA_MAX=2. Every Lean call has -j1 -M3500 -DwarningAsError=true, and the subprocess Lean wrapper also supplies -j1 -M3500. Only one heavy process runs at a time. The watchdog is reaped. TMPDIR and caches are extraction-local. Each invocation retains unique .out/.err logs under logs/.

Lean is /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean. Mathlib packages are the pinned d13f23b723b8a846827a245b89c10fc7d3f11612 read-only installation under the 2026-10-14/formal/.lake/packages directory. The base source archive was verified as SHA256 9dc97086dd29e29d7d84932df93256c01c4531b9813e0be7f16af8410d589e6c.

The driver strictly builds all 23 modules serially, running leanchecker with each explicit module argument. It verifies the 20 inherited file hashes before and after. Antimagic4BAudit imports the final endpoint and regressions; it traverses all local declarations and their transitive dependency closure, including opaque values, generated declarations, constructors, declaration groups and _unsafe_rec companions. Closure equality is checked by construction and explicit edge membership checks. report4b.py verifies allowed axioms, local metadata, hash integrity and declaration uniqueness, then writes results.json. Upstream metadata is kept separate. The inherited Python regression covers 42 cases and duplicate-label, l-colour and odd-t negative controls. Finite tests serve only as regressions.

The delivered fresh extraction is replay-fresh/. Its logs, audit.tsv and results.json record the clean replay; the lane-root results.json is the corresponding report. The archive contains only source modules, scripts, documentation, manifests and the report. It excludes build objects, caches and logs. source.zip.sha256 records the archive digest. Root retains responsibility for independent review and acceptance.
