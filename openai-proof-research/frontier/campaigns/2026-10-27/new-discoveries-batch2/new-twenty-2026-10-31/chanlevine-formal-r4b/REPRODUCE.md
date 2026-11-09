# Reproduction

The source archive is chanlevine-round4b-source.zip. Extract it into a new empty directory inside this lane and run `python3 -I scripts/replay.py --resume`. It rebuilds all 24 modules in dependency order, with Lean 4.34.1, `-j1 -M3500 -DwarningAsError=true`, then leanchecker on each module. Fingerprinted receipts permit resuming identical sources.

Lean: /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean.
Pinned read-only mathlib package cache: /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages, revision d13f23b723b8a846827a245b89c10fc7d3f11612.

Each expensive child process runs through scripts/cap.py with CPUs 0 and 1, CPU limit 120 seconds, wall limit 140 seconds, and monitored process-group RSS capped at approximately 6 GiB. MALLOC_ARENA_MAX=2. TMPDIR, build, and cache directories are extraction-local. All processes are serial, with uniquely named retained logs.

Sem4Audit audits all declarations in the local import closure of SemFinal3 and recursively visits their type and opaque-body dependencies and constructor edges. Replay recomputes closure equality and reports local flags separately from upstream extern/implemented_by metadata. It checks six negative controls and the reviewer-based 18-case SCC regression, including new capped-word checks.

SemFinal3 is conditional: cycleTestBridge assumes CappedDeficitTrap; connectedFibres assumes RecurrentNormalization. No unconditional MathDB endpoint is claimed. See SUMMARY.md for the exact remaining work. Root alone decides acceptance.
