# Reproduction

Use Lean 4.34.1 at /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin and the read-only mathlib package cache at /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages (mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612).

All commands and outputs must stay inside this lane. The delivered source archive is chanlevine-round5a-source.zip. scripts/package.py checks the frozen hashes, creates the source-only archive, validates safe paths, and extracts to a new empty lane-local directory. Do not extract into a directory containing build artifacts.

Run `python3 -I fresh-extraction/scripts/replay.py --resume` from the lane directory. The script sets lane-local TMPDIR and XDG_CACHE_HOME, the pinned LEAN_PATH and MALLOC_ARENA_MAX=2. Every heavy invocation uses scripts/cap.py: at most two CPUs, CPU 120 seconds, wall 140 seconds, managed RSS 6 GiB, strictly serial. Lean runs with -j1 -M3500 -DwarningAsError=true. Unique logs are retained. A receipt is reused only when its full source fingerprint matches.

The ordered 29-module replay compiles each module and runs leanchecker on each. CountR5Audit computes the reachable type/value declaration closure from all local endpoint/control declarations, including generated declarations; it checks closure membership of every dependency and records flags and allowed axioms. The replay checks audit row counts and the source import closure independently. Upstream executable metadata is reported separately from local flags.

Negative controls reject wrong rotation, missing rotor factor, wrong parity, and attempted use of the new conditional spectralOrder/unitCount as unconditional proofs. Exact Python diagnostics run in isolated mode, retaining 104 inherited positive-level cases and new top/rotor checks. `scripts/finalize.py` reads the fresh replay receipts and logs, verifies extraction and frozen hash identity, and writes results.json and upstream-flagged-declarations.txt. The top-level results.json is generated after replay and is intentionally outside the source-only archive.

This is a partial certificate: exactly Round3.TransferCountEvaluation remains unproved. The archive and replay do not establish unconditional spectralOrder or unitCount.
