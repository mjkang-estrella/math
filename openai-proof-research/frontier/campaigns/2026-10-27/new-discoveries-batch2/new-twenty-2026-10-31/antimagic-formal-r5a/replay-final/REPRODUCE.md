# Resumable round 5A replay

Run from this lane or a fresh source.zip extraction:

    bash scripts/replay5a.sh

Resume an interrupted replay, within the same extraction:

    RESUME=1 bash scripts/replay5a.sh

The resume driver skips a module only when its checked marker is newer than its
source. Remove build/*.checked to force all kernel checks. After editing a
dependency, remove checked markers for all dependent modules (or use a fresh
extraction); this is a replay convenience, not a dependency-aware build system.

The driver rebuilds 37 modules strictly and serially, with an explicit
leanchecker module argument after every build. The last audit module enumerates
the full local declaration dependency closure including opaque values, generated
declarations and unsafe_rec companions, verifies closure, and writes audit.tsv.
The report checks allowed axioms and local executable metadata and records
upstream metadata separately. It also checks all 27 inherited hashes and runs
the inherited regression script and the nine requested higher-depth cases with
two negative controls. results.json is generated only after all these pass.

The Lean binary is pinned to
/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean.
The read-only mathlib package tree is
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages,
revision d13f23b723b8a846827a245b89c10fc7d3f11612.
No package download, git, network, or browser operation is required.

scripts/capped.sh runs every Lean, leanchecker and python3 -I process under a
6 GiB process-group RSS watchdog, CPU 120 seconds, wall 140 seconds, taskset CPUs
0,1 and MALLOC_ARENA_MAX=2. Every Lean call has -j1 -M3500 and warningAsError.
TMPDIR, caches, generated files, builds and uniquely named full logs stay in
the current extraction. The watchdog is reaped after every process exits.

The fresh replay performed for this handoff is in replay-final, with its complete
replay-driver.log, logs/, audit.tsv and results.json. The source-only archive
contains safe relative paths and no compiled artifacts. inherited-before.sha256
and inherited-after.sha256 contain all 27 frozen modules and compare equal.

Development logs retain failed attempts as well as successful checks. One early
import-only compile was launched while the serial inherited build had not yet
reached its import; it failed immediately with an unknown-module error. Later
Lean calls and the extracted replay are serial. No such failed attempt is used
as validation evidence. No background work is left at handoff.
