# Reproduce r2b

Use Python 3 with `-I`. The pinned Lean binary is `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`, version 4.34.1; sibling leanchecker is used. The read-only package cache is `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`, with supplied mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The delivered replay has already been initialized and completed. `replay-state.json` records the archive hash, completed jobs, log hashes, and every build-object hash. `manifest.json` records source and toolchain hashes. `replay/extracted/` was initially empty, and contains only the fresh archive extraction and its resulting logs/builds. Package contents have relative safe paths and no build objects.

To verify the recorded state, from this lane run:

```sh
python3 -I scripts/replay.py --resume --steps 1
```

To independently rebuild without reusing objects, create a new empty directory **inside this lane**, copy `pdtar-source.zip` into it, create its `scripts/` directory, and copy `scripts/replay.py` there. Run this copied driver from the new directory:

```sh
python3 -I scripts/replay.py --init
python3 -I scripts/replay.py --resume --steps 1
```

Repeat the second command until Progress 29 / 29. Larger `--steps` batches are supported; every Lean/checker invocation remains serial and separately capped. No background job is started. `--init` refuses an existing extraction. Resume validates archive/source/toolchain, completed logs and build-object hashes before progressing.

Dependency order: Defs, Basic, FortDuality, KstFamily, Core, Remaining, ReductionTransport, ReductionFlip, ReductionCube, ReductionBasis, ReductionMetric, ReductionPaths, ReductionProof. Then run leanchecker on those 13 modules, compile scripts/Audit.lean, and run the two expected-failure controls. All commands go through scripts/limited.py. Compiler flags are `-j1 -M3500 -DwarningAsError=true -DElab.async=false`.

Read `replay/extracted/logs/audit.log` for all 159 mathematical declarations including generated ones, their safety flags and complete transitive axiom sets. The audit driver rejects any violation. The two negative controls must fail at the mathematical proof, not at an unknown constant or missing import. The replay driver checks their expected failure categories.

Frozen-source hashes before and after are in frozen-before.json and frozen-after.json. scripts/package.py documents source-only archive creation. Do not regenerate the delivered archive before checking its recorded hash.
