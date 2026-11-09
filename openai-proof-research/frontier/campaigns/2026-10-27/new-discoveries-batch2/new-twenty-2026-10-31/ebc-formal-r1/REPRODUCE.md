# Reproduction

Pinned Lean: 4.34.1, installed at
`/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin`.
Pinned read-only mathlib packages:
`/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`,
mathlib revision specified by TASK.txt: d13f23b723b8a846827a245b89c10fc7d3f11612.
No network, lake build, git, or dependency writes are needed.

From the lane:

```
bash scripts/replay.sh
```

This extracts source-only.zip into a fresh lane-local replay directory, then
reads module-order.txt. Each module gets one lean process and a separate
leanchecker process with that explicit module argument. Compilation uses
`-M3500 -DwarningAsError=true`. The audit module prints local declaration
metadata and endpoint axioms. The resumable command is:

```
RESUME=1 bash scripts/replay.sh
```

Use a different absolute lane-local extraction path as the optional first
argument for an independent fresh replay. Do not use RESUME after editing
sources. Only source archive files are extracted; no prebuilt oleans are
packaged. Logs and PASS markers are written in the extraction.

scripts/env.sh configures lane-local TMPDIR and XDG_CACHE_HOME,
MALLOC_ARENA_MAX=2, read-only dependency lookup and the two-CPU taskset.
scripts/cap.pl monitors the process group RSS at 6 GiB and kills its group at
140 s wall; every cap call also applies ulimit -t 120. No limits are raised
on failure. Run calls serially. The watchdog is reaped before return.

The first development import of all Mathlib exceeded the memory limit and
was stopped. Imports were reduced to the needed files. A single rational
arithmetic module exceeded the CPU cap, so rational rows were split into
eight modules; the caps were not raised. Development error logs are retained.
Final source scanning excludes prose and audit string literals from token
bans, but scans every Lean source for forbidden commands/tactics. Metadata
inspection also rejects locally generated disallowed helpers.

scripts/generate.py and split.py record development generation, not replay
requirements. Replay uses the final checked Lean files directly. A fresh
Lean build is the authoritative computation certificate; independent Python
output is diagnostic only.
