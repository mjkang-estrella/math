# Reproduction

Extract ulas-source.zip into an empty directory inside this lane and run
`bash <extraction>/scripts/replay4.sh`. No network or lake update is needed.
The script builds 21 modules strictly serially in dependency order, using
Lean 4.34.1, -j1 -M3500 -DwarningAsError=true. It resumes completed modules,
runs leanchecker on each, eight full declaration-export audit shards,
closure equality and transitive-axiom analysis, four exact Python regressions,
and three deliberately failing negative controls.

The runner fixes CPUs 0 and 1, MALLOC_ARENA_MAX=2, CPU 120 seconds,
wall 140 seconds, and monitored RSS at most 6 GiB per heavy process.
TMPDIR, XDG_CACHE_HOME, builds and logs are lane-local. No heavy processes
run concurrently. Logs use distinct names. The outer replay driver is serial.

The package cache is read-only at
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages,
pinned mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
The Lean binary is /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean.

Audit LOCAL and upstream metadata are reported separately. The audited set
is compared with all declarations in the endpoint's entire import closure,
including generated declarations and opaque values. Compiler IR extra names
are separately inventoried. Only propext, Classical.choice and Quot.sound
are allowed in LOCAL transitive axiom sets. Frozen audit instrumentation is
rebuilt and kernel-checked as well as mathematical modules.
