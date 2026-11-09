# Reproduction

Pinned Lean: 4.34.1, `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin`.
Pinned Mathlib: d13f23b723b8a846827a245b89c10fc7d3f11612, packages at `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages` (read only). The source package has no vendored or modified dependencies.

Extract `source.zip` into a fresh directory inside the assigned lane, enter it, and run `./replay.sh`. Run `./replay.sh resume` to resume after a successful module; delete stale `logs/*.replayed` markers after changing any source. `module-order.txt` is the dependency order. Each module is compiled separately with `lean -M3500 -DwarningAsError=true`, then separately checked by `leanchecker ModuleName`. The explicit module argument is mandatory. The script stops on any failure.

For a single module: source `env.sh`, then run `./bounded.sh lean -M3500 -DwarningAsError=true -o build/General.olean General.lean`, followed by `./bounded.sh leanchecker General`. Change the module name according to the order file. Create build/logs/tmp first if not using the driver.

`bounded.sh` enforces taskset CPUs 0 and 1, 120 CPU seconds, 140 wall seconds, aggregate process-group RSS at most 6 GiB (sampled every 0.3 seconds), MALLOC_ARENA_MAX=2, lane-local TMPDIR, and PYTHONDONTWRITEBYTECODE=1. It disables core dumps and reaps its watchdog. There is one heavy process at a time. No network, git, or child agents are used.

The final Audit module prints endpoint and control axiom dependencies and rejects forbidden local declaration metadata. Source scans and final results are recorded alongside the extracted replay, outside the source-only archive. Development attempts hitting memory limits are summarized in results.json. No resource limit was raised.
