# Reproduce

Lean 4.34.1:
/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin

Read-only packages:
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
Mathlib revision from TASK.txt: d13f23b723b8a846827a245b89c10fc7d3f11612.
No network, git, lake build, or dependency mutation is required.

From this lane run `bash scripts/replay.sh` for a fresh extraction at
replay-final (which must not exist). An alternative unused absolute lane-local
path can be its first argument. To continue an interrupted extraction run
`RESUME=1 bash scripts/replay.sh`. Do not resume after changing the archive.
Each module in module-order.txt has its own Lean process with
`-M3500 -DwarningAsError=true`, then a separate explicit-module leanchecker.
PASS markers are written only after both succeed. The archive contains only
source, scripts, documentation and the module order, with no build products.

scripts/env.sh sets lane-local TMPDIR and XDG_CACHE_HOME, MALLOC_ARENA_MAX=2,
PATH and read-only LEAN_PATH dependencies. cap applies taskset to CPUs 0,1,
ulimit CPU 120 s, and scripts/cap.pl monitors RSS at 6 GiB and wall 140 s,
killing and reaping the process group on a violation. Use cap for every Lean,
leanchecker and Python invocation. Processes run serially; do not increase
limits after failures. No background jobs are left at handback.

After replay, generate the source scan and results with:

    source scripts/env.sh
    cap python "$LANE/scripts/report.py"

The report checks all 20 compile/checker markers, the metadata audit, endpoint
axioms, forbidden source tokens, archive paths, and byte identity against the
round-1 archive. It records the source archive hash and every source hash.
All Python is in a real lane-local script, not stdin. The driver and watchdog
were written in this lane; no other lane's scripts are run.

Development failures are retained separately in logs; the authoritative strict
fresh-extraction logs are replay-final/logs. No resource limit was increased.
The optional C_21 control was omitted; the original C_2 control is unchanged.
