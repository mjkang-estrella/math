# Round 3 reproduction

No network or installation. Lean 4.34.1 is pinned at `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin`; package oleans are read only at `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`, mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612.

Extract `source.zip` into a NEW directory inside delta-formal-r3. From that extraction run `bash scripts/replay.sh`, or `bash scripts/replay.sh --resume` after interruption. Each module compiles in its own process and is checked with explicit-module leanchecker before its success marker is written. Never run concurrent replay drivers. After changes to sources or dependencies use a fresh extraction. A STOP_REPLAY file in the lane stops at the next checked module boundary.

The driver uses two CPUs, CPU 120 seconds, wall 140 seconds, a 6 GiB process-group RSS watchdog, MALLOC_ARENA_MAX=2, lane-local temporary and cache directories, disabled core dumps and `lean -j2 -M3500 -DwarningAsError=true`. Target and watchdog are reaped. Logs include process exit status and `/usr/bin/time -v` resource measurements. Python verification/generation processes use the same wrapper. Limits must never be raised.

`bash scripts/source-scan.sh` runs the source token scan. Audit, Round2Audit and Round2AuditPartial inspect declaration metadata; Round2Audit prints the unconditional endpoint axiom dependencies. Only propext, Classical.choice and Quot.sound are permitted. Full replay includes all audits in modules.txt. The source zip contains no objects or success markers.

`changes.json` records original and final SHA256 hashes for every changed round 2 archive file and lists every unchanged file. `logs/changes.diff` is the complete textual diff. `scripts/report.py` independently verifies that deleting new census helper proofs and reverting only the census proof bodies exactly reconstructs each original Lean file. Graphs, children, lower-bound proofs and all original theorem statements are byte unchanged.

Root decides acceptance. Development using inherited objects is not a fresh replay receipt.

The delivered archive's completed fresh replay is in `fresh/`; `fresh/logs/replay/*.ok` and the corresponding Lean/checker logs cover all 634 modules. `replay-table.csv` records each process's RSS and wall time. Run `bash fresh/scripts/replay.sh --resume` to verify the recorded checkpoint without rebuilding, or extract the ZIP into another new lane-local directory for an independent full replay. The ZIP is immutable after its recorded replay; the lane's SUMMARY.md and results.json carry the final outcome separately.
