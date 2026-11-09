# Replay

Extract wheel-lower-source.zip to a fresh directory. Set LEAN_BIN to the Lean executable at version 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52. Set LEAN_PACKAGES to the read-only mathlib package directory pinned at d13f23b723b8a846827a245b89c10fc7d3f11612. Run `python3 -I replay.py`. No network is used. The driver refuses any existing .olean, verifies the source manifest, constructs a sanitized environment, and uses strict Lean with one worker. It rebuilds all seven modules, audits every declaration in those modules (including generated declarations), invokes leanchecker on all seven, and runs four failing Lean controls plus a dirty-extraction refusal control. Only propext, Classical.choice and Quot.sound may occur transitively.

Every expensive call is limited to two CPUs, 120 CPU seconds, 140 wall seconds, and sampled aggregate private RSS of 6 GiB. The guard uses a 64 GiB address-space limit, samples /proc every 0.1 seconds, and records receipts beside full logs. MALLOC_ARENA_MAX is 2. No background processes remain after replay. Source manifest excludes itself.

The two r1 modules are byte-identical. Input provenance hashes are in inputs-before.json and inputs-after.json. This packet proves the lower bound only; equality and the upper construction are outside r2a scope. Root acceptance is pending and credit is zero.
