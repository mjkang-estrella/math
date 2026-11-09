# Reproduction

Extract chanlevine-round5b-source.zip into a new empty directory inside this lane. Run `python3 -I scripts/replay.py --resume` from that extraction. The replay serially rebuilds all 30 modules with strict warnings, checks every module with leanchecker, checks declaration closure equality, runs eight negative controls, and runs the 18-case SCC and normalization regressions. Fingerprinted receipts allow exact-source resumption.

Lean binary: /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean.
Read-only mathlib cache: /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages, pinned revision d13f23b723b8a846827a245b89c10fc7d3f11612.

Each expensive child runs through scripts/cap.py: CPUs 0 and 1, CPU 120 seconds, wall 140 seconds, monitored process-group RSS about 6 GiB, MALLOC_ARENA_MAX=2. Lean uses -j1 -M3500 -DwarningAsError=true. TMPDIR, caches, builds and unique logs remain extraction-local. Processes are serial.

SemFinal4 proves cycleTestBridge and connectedFibres unconditionally. Sem5Classify proves the exact RecurrentNormalization; Sem5Trap proves the exact CappedDeficitTrap. The independent counting obligations remain outside this lane. Root decides acceptance.
