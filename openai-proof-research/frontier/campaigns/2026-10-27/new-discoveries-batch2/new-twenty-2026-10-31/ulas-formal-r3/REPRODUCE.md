# Reproduction

Pinned Lean: /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin. Read-only package cache: /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages, mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612.

Extract ulas-source.zip into a new empty directory INSIDE this lane, then run `bash <extraction>/scripts/replay3.sh`. This script derives its lane from its own location. It builds strictly serially in dependency order, resumes from completed modules, runs eight declaration-export audit shards, runs leanchecker on each module, validates closure equality and transitive axioms, runs three exact Python regressions and two intentionally rejected negative controls.

Each expensive child is run via run.sh and bounded.py: CPUs 0 and 1, CPU 120 seconds, wall 140 seconds, monitored RSS 6 GiB, MALLOC_ARENA_MAX=2; Lean uses -j1 -M3500 -DwarningAsError=true. TMPDIR and XDG_CACHE_HOME stay inside the extraction. Logs have unique nanosecond names. Every heavy child runs serially. The outer shell is a resumable driver, not a heavy process.

The archive contains only source and scripts. The fresh-replay directory was empty before extraction. Frozen modules are included byte-identically; frozen-before.json and frozen-after.json bind all nine inherited source files to the round-2 packet. The nine include audit instrumentation, while the endpoint mathematical closure includes seven inherited mathematical modules and two new ones. UlasAudit3 is new audit instrumentation.

The LOCAL audit covers generated declarations as well as named theorems and excludes upstream metadata from its safety verdict. The analyzer explicitly compares the audited set with all const_names of the endpoint module import closure and computes transitive axioms to a fixed point, allowing opaque values. Compiler IR extra names are inventoried separately.
