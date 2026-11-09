# Resumable round 6A replay

From this lane, or an empty directory with source.zip freshly extracted:

    bash scripts/replay6a.sh

Resume within an unchanged extraction:

    RESUME=1 bash scripts/replay6a.sh

The driver rebuilds 45 modules strictly and serially and invokes leanchecker
with each explicit module name. Resume skips a source only when its checked
marker is newer; after dependency edits remove dependent markers, or use a
fresh extraction. This is not a dependency-aware build system.

Lean is pinned to /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin.
Mathlib packages are read-only at
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages,
revision d13f23b723b8a846827a245b89c10fc7d3f11612.
No download, git, browser, upload or external message is needed.

Every Lean, leanchecker and Python process runs through scripts/capped.sh:
two CPUs (0,1), CPU 120 seconds, wall 140 seconds, 6 GiB group RSS watchdog,
MALLOC_ARENA_MAX=2, lane-local TMPDIR and caches. Every Lean invocation uses
-j1 -M3500 -DwarningAsError=true. There is one heavy process at a time;
the wrapper reaps its watchdog. Full uniquely named stdout/stderr logs are kept.

The final audit reads opaque bodies, includes generated declarations and
unsafe_rec companions, verifies closure and records local versus upstream
metadata separately. report6a.py checks the allowed axiom set and absence of
local unsafe/partial/implemented_by/extern/unsafe_rec metadata, all 37 inherited
hashes and all 45 build/check markers. Numerical checks and inherited negative
controls run under the same caps. Audit and results are generated afresh.

The fresh replay for this handoff is replay-final, with replay-driver.log,
logs/, audit.tsv and results.json. Development logs retain failed proof attempts;
only successful strict builds and explicit checks constitute validation.
