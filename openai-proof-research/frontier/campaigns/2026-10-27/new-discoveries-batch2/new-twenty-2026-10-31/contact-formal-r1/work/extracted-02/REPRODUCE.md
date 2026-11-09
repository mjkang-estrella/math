# Replay of a partial pilot, not a conjecture certificate

Extract `contact-pilot-source.zip` into a new empty directory inside this lane.
Run with Python 3 in isolated mode:

```bash
LEAN_BIN=/path/to/lean-4.34.1-linux/bin/lean \
LEAN_PACKAGES=/path/to/pinned/.lake/packages \
python3 -I -B scripts/replay.py
```

`LEAN_BIN` must point to Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52.
`LEAN_PACKAGES` must contain mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612
and its matching cached dependencies. The driver does not download or alter them.
It refuses any existing local olean, ilean, ir or build directory; builds all
four source modules sequentially with `-j1 -DwarningAsError=true`; runs leanchecker;
prints every local declaration (including generated declarations), its defining
module, full raw expression type and opaque-inclusive body, unsafe/partial flags,
and transitive axioms. It rejects unapproved axioms or unsafe/partial declarations.
Audit infrastructure is not part of the mathematical theorem claim.

Every compiler/checker process runs under the watchdog: at most two available
CPUs, CPU 120 seconds, wall 140 seconds, sampled private RSS 6 GiB,
MALLOC_ARENA_MAX=2. Samples and complete stdout/stderr are retained in replay-logs.
The watchdog samples the direct process; these Lean/checker invocations launch
no child compilation processes. No server or asynchronous worker is used.

Three expected-failure controls reject a false square-root equality, a wrong
residual constant, and contact for a nonvanishing constant numerator. A successful
replay certifies only the partial declarations, never `¬ SourceConjecture`.
The failed developmental attempts are outside formal/ and outside the packet.
