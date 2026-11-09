# Reproduction

Extract ulas-source.zip into a new empty directory within this lane. Run
`bash <extraction>/scripts/replay5.sh`. It resumes completed modules and builds
strictly serially with Lean 4.34.1, -j1 -M3500 -DwarningAsError=true, runs
leanchecker, eight audit shards, closure equality, and regression/negative
controls, including regression5.py and the three round-5 negative controls. All builds, temporary
files, caches and logs remain under the extraction directory. The runner caps
each expensive process at CPUs 0,1, CPU 120 s, wall 140 s and monitored RSS
6 GiB, with MALLOC_ARENA_MAX=2. No heavy processes are concurrent.

The Lean binary and read-only pinned mathlib package paths are those specified
in TASK.txt and scripts/run.sh. No network or lake updates are required.
The archive contains source and scripts, not object files. Development failures
are retained in logs; the fresh extracted logs are the authoritative replay.
LOCAL and upstream declaration metadata are audited separately. The audit
includes opaque values and generated names and compares its set with the full
endpoint import closure. Only propext, Classical.choice and Quot.sound are
allowed for LOCAL transitive axioms.
