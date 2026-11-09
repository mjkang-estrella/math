# Reproduction

Use Python 3 with no third-party packages. Lean is /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean. Read-only pinned mathlib packages are /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages, revision d13f23b723b8a846827a245b89c10fc7d3f11612.

Run `python3 -I scripts/package.py` once from this lane to create the source-only zip and a new empty fresh-extraction directory. Run `python3 -I fresh-extraction/scripts/replay.py --resume`. Each Lean and leanchecker subprocess is serial, capped at 2 CPUs, CPU 120 seconds, wall 140 seconds and approximately 6 GiB RSS; Lean uses -j1 -M3500 -DwarningAsError=true. MALLOC_ARENA_MAX=2 and TMPDIR/cache paths are lane-local. Logs use unique names. Resume receipts bind to all source hashes. No network or writable mathlib cache is needed.

The audit logs list every reachable declaration, flags and generated locals, verify closure containment and allowed axioms, and print the conditional theorem types. Upstream extern/implemented_by metadata is retained separately and must not be described as absent. Negative controls intentionally fail compilation. These are validation of a partial conditional packet, not evidence of unconditional endpoints.
