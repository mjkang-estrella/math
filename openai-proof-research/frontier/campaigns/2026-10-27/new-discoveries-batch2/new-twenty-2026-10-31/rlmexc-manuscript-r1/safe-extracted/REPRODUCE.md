# Reproduction

Lean 4.34.1:
`/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin`.
Mathlib is the read-only installation in
`/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib`,
pinned d13f23b723b8a846827a245b89c10fc7d3f11612. The companion package build
paths are discovered read-only by `scripts/env`. No Lake build or downloads
are required. All output paths are relative to the extracted lane directory.

Extract `source.zip` into a fresh directory under this lane and run:

```bash
bash scripts/replay
```

The driver reads `module-order.txt`. It compiles one module per process with
`lean -M3500 -DwarningAsError=true`, then runs `leanchecker ModuleName` for
that exact module. Each invocation uses the capped wrapper; stdout, stderr
and `/usr/bin/time -v` measurements go into `logs/`. Checker success is exit
code 0, enforced by `set -e`; `logs/last-completed.txt` records progress.

To resume after interruption, preserve the existing build directory and run,
for example, `bash scripts/replay Characterization`. Resume begins at the
named module, including its compile and checker step. To start fresh, extract
again rather than reusing compiled artifacts. The archive includes no oleans.

The wrapper uses a lane-local flock to serialize heavy commands, two CPUs
from the current allowed CPU range, `ulimit -t 120`, a 140 s wall timeout,
RSS sampling with a 6 GiB kill threshold, `MALLOC_ARENA_MAX=2`, and lane-local
TMPDIR. It disables core dumps. It never invokes a checker without a module.
Do not run unrelated heavy commands outside this wrapper during replay.

`Audit.lean` prints the endpoint and control axioms and inspects every local
constant (identified by its defining module, including generated declarations)
for unsafe/partial metadata, implemented-by and extern attributes, generated
unsafe recursors, and new assumptions. The source scan is recorded separately.
All generated helper definitions are audited, not just named theorems.
