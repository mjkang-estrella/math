# Reproduction

Pinned Lean: /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin. Read-only pinned packages: /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages, mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

From this lane run `python3 -I scripts/package.py` once to verify all 36 frozen hashes, create chanlevine-round7t-source.zip with safe relative paths, and extract into a new empty fresh-extraction directory. Run `python3 -I fresh-extraction/scripts/replay.py --resume` for strict serial compilation and leanchecker for every module. Without --resume it rebuilds everything. Source-manifest receipts permit a strict replay to resume. Run `python3 -I scripts/finalize.py` after replay to collect results.json and the separate upstream flag listing.

Every expensive child is run through scripts/cap.py, with two CPUs, CPU 120 seconds, wall 140 seconds and aggregate RSS 6 GiB. TMPDIR and caches are lane-local. All Lean compilation uses -j1 -M3500 -DwarningAsError=true. The replay independently derives the local source import closure and compares it with the audited module set. The audit traverses declaration types and values, including generated declarations, checks all outgoing dependency membership and permits only the three standard axioms. Upstream executable metadata is reported separately.

Seven negative controls must fail compilation, including a wrong trace sign and an incorrect alternating matching. The original exact diagnostics and scripts/check_r7t.py run serially under the same caps. Controls are not extra assumptions of the theorem. No MathDB endpoint acceptance is asserted.
