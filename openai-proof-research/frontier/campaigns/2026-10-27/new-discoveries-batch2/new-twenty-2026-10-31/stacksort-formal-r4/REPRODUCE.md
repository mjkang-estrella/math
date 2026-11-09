# Reproduction

Pinned toolchain: Lean 4.34.1 at /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin; mathlib packages read-only at /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages, pin d13f23b723b8a846827a245b89c10fc7d3f11612.

Extract stacksort-source4.zip into a new empty directory inside this lane. From that extraction run `bash scripts/replay4.sh`. It strictly builds all 73 modules serially, invokes leanchecker with each explicit module name, and runs check_audit4.py. The build is resumable, preserving already completed olean files. For an independent replay, use an empty extraction rather than the implementation build directory.

Every Lean, leanchecker and Python invocation must go through scripts/run.sh. It sets the lane-local TMPDIR and caches, MALLOC_ARENA_MAX=2, CPU affinity 0,1, CPU limit 120 seconds, wall limit 140 seconds, and an aggregate process-tree RSS watchdog at 6291456 KiB. The monitor is stopped and waited after every command. All Lean build calls specify -j1 -M3500 -DwarningAsError=true. Never invoke leanchecker without a module argument. Run one heavy process at a time.

The audit module uses allowOpaque=true to traverse declaration values, records all kernel declarations and compiler-generated symbol names, and rejects disallowed local metadata or local transitive axioms. The Python verifier computes the exact import closure of StackSortFinal4, compares its complete declaration-name set with the audited set, checks metadata, and traverses every new endpoint/helper dependency. It reports LOCAL and upstream metadata separately.

The inherited negative controls remain in the final import closure. They reject wrong seed values, the wrong base, the threshold 1.95, the wrong sorting convention, and incorrect recurrence rows. No P5 or P6 literal kernel regression is newly claimed.

The fresh-extraction/ directory retains the strict replay logs, explicit module checker logs, raw declaration audit, closure report and compiler-symbol inventory. The 66 inherited source hashes are recorded before and after in hashes/; these manifests must compare byte for byte. The source zip contains only safe relative source and script paths, with no compiled artifacts.
