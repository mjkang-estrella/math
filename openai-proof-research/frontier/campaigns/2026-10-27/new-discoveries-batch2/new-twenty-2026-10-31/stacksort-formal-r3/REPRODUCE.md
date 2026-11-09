# Reproduction

Use Lean 4.34.1 at the binary path in TASK.txt and read-only mathlib packages pinned to d13f23b723b8a846827a245b89c10fc7d3f11612. scripts/run.sh sets the search path to the current source directory and those package build directories; no lake build or dependency update occurs.

From an extraction root, create logs, tmp and cache, then run `bash scripts/replay.sh`. scripts/build.sh compiles serially in scripts/order.txt order and resumes from existing successful olean files. Every Lean call uses -j1 -M3500 -DwarningAsError=true. Each audit module receives a lane-local STACKSORT_AUDIT_OUT path. The replay invokes leanchecker with an explicit module argument for every module, then the full declaration-closure audit script under the same watchdog.

scripts/run.sh constrains every Lean, leanchecker and Python process to CPUs 0,1, CPU 120 seconds, wall 140 seconds and aggregate process-tree RSS 6291456 KiB. It sets MALLOC_ARENA_MAX=2, TMPDIR and cache locations within its extraction root, disables Python bytecode writes and core dumps, and retains uniquely named full logs. Its watchdog is terminated and waited after each process. Run only one such heavy call at a time.

stacksort-source3.zip contains source modules and replay scripts, no olean files or compiled artifacts. fresh-extraction is a newly created extraction used for the independent strict rebuild and explicit checkers. hashes/inherited-before.sha256 and inherited-after.sha256 record the unchanged inherited tree. Packet SHA-256 checks are in hashes/packets.sha256. results.json records module hashes, line counts, endpoint status and audit totals.

Inherited StackSortControls, StackSortInj2Controls and StackSortSeeds2Controls retain the negative controls: wrong seed, wrong certificate base, 1.95 threshold, wrong sorting convention, wrong lower row, and wrong recurrence table entries. All are compiled in the endpoint import closure. Literal P5/P6 kernel regressions remain unfinished inherited limitations; no claim is made to have closed them here.
