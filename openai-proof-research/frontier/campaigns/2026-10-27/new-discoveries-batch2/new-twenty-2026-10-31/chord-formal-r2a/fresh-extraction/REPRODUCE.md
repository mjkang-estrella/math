# Reproduction

Lean is /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin, version 4.34.1. Read-only mathlib packages are /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages, designated pin d13f23b723b8a846827a245b89c10fc7d3f11612. No git, package update or network access is used.

Extract chord-source.zip into a new empty directory INSIDE chord-formal-r2a. Run scripts/rebuild.sh there. The script builds the 41 formal modules in modules.txt serially, followed by ChordModel2Audit, and invokes leanchecker with the explicit module name each time. It stores success hashes for resumability. If a dependency changes, clear subsequent success markers. All archived sources are immutable for the recorded replay.

Every Lean, leanchecker and Python process must run through scripts/capped.sh. That wrapper sets lane-local TMPDIR/cache, MALLOC_ARENA_MAX=2, taskset -c 0,1, CPU 120 seconds, wall 140 seconds, and a process-group RSS watchdog killing above 6 GiB. Lean always receives -j1 -M3500 -DwarningAsError=true. Only one heavy process runs at once. Complete uniquely named logs are retained.

Run scripts/capped.sh python3 -I scripts/regression.py for the independent inherited regression, including negative controls. It checks both boundary models, exact Euler parity/nonnegativity, and source counts through five chords. This is computational evidence, not a new proof of the open generic bridge.

ChordModel2Audit examines the exact import closure of ChordModel2Final, including generated declarations and opaque values. It compares the audited set with imported module inventories and rejects every forbidden LOCAL flag, implementation hook, generated unsafe companion or transitive axiom. Only propext, Classical.choice and Quot.sound are allowed for LOCAL declarations. Upstream implementation metadata are reported separately. The audit inspector itself is a tool, outside the endpoint closure.

Compare sha256sum of each inherited src/Chord*.lean file against frozen-before.sha256 and the original archive. results.json provides hashes and line counts. No object files or third-party packages appear in the source-only archive.
