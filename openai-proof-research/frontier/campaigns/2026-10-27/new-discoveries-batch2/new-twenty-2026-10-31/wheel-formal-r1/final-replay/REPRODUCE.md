# Reproduction

Extract wheel-partial-source.zip into a **new empty directory**. The driver refuses any existing .olean beneath its directory, validates source hashes, and builds with a sanitized environment, one Lean worker, warningAsError, and per-process resource guards. All writes remain under the extraction directory. Dependencies are read-only.

Set LEAN_BIN to the full Lean executable and LEAN_PACKAGES to the directory of package caches:
    
    LEAN_BIN=/path/to/lean-4.34.1/bin/lean LEAN_PACKAGES=/path/to/.lake/packages python3 -I replay.py

Required Lean is 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52. The source was compiled against mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. The dependency revision is an externally supplied pin, not inferred from cached olean metadata. The replay verifies the Lean version/commit, not the mathlib Git revision; supply the stated read-only cache.

The driver runs strict source compilation, all-declaration audit, leanchecker for both proof modules, and negative controls. It creates logs with process receipts. Each guarded process has two-CPU affinity, a 120-second CPU limit, 140-second wall limit, sampled aggregate private RSS limit of 6 GiB, and 64-GiB address space. MALLOC_ARENA_MAX=2. Sampling is every 0.1 seconds and is not a continuous RSS bound.

This is a source-only packet for PARTIAL components. Successful replay does not prove Conjecture 7.3. WheelFormal.Target is only a proposition definition. See GAPS.md.

An initial leanchecker --help probe was treated by that executable as an anonymous module query and was killed by the RSS guard at a sampled 6.515 GiB (receipt logs/leanchecker-help.log.receipt.json). It is not a verification success. The explicit module checks completed within the guard.
