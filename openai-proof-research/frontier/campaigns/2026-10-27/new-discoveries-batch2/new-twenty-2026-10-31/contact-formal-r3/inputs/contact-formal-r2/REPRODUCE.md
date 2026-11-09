# Replay of a partial formalization

The packet certifies partial theorems only. It contains no `¬ SourceConjecture`.

Extract `contact-r2-source.zip` into a NEW EMPTY directory inside this lane.
Then, from the extraction, run:

```bash
LEAN_BIN=/path/to/lean-4.34.1-linux/bin/lean \
LEAN_PACKAGES=/path/to/pinned/.lake/packages \
python3 -I -B scripts/replay.py
```

Use Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, and
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 with matching cached
dependencies. The driver uses the supplied paths and changes no dependencies.
It refuses pre-existing oleans, ileans, ir files or a build directory. It
sanitizes every module, compiles nine modules sequentially with
`-j1 -DwarningAsError=true`, runs leanchecker on each, audits every local
module's declarations including generated ones, and runs six expected-failure
controls. Audit logs the full raw type and opaque-inclusive body, module,
unsafe and partial flags, and transitive axioms; only propext, Classical.choice
and Quot.sound are allowed. Both inherited Audit.lean and new AuditR2.lean
are retained. Large full logs are archived losslessly with gzip.

The compiler and checker use the watchdog for every call: affinity at most
two CPUs, CPU 120 s, wall 140 s, sampled private RSS 6 GiB,
MALLOC_ARENA_MAX=2. Receipt files contain every sample. Each compilation and
checker is a direct process with no child workers. Only one such process
runs at a time. No server is used.

`complete.json` records module source hashes and control counts. The packet
contains only source, drivers, and these reproduction/gap documents. Inputs,
development builds, failed logs and generated oleans are outside the packet.
Successful replay certifies the partial results and cannot establish the
missing reduced bidisk certificate or the source refutation.

AuditR2 writes `replay-logs/audit-r2.dag` directly. Within each DECL block,
TYPE_REF and BODY_REF point to numbered NODE entries (BODY_NONE records a
declaration without a value). Node IDs are local to the block. All Expr
constructors, binders, universe levels, literals and metadata are preserved.
This is a lossless expression DAG, not a body summary or a list of constants.
END_DECL closes each block. It avoids expanding shared proof terms repeatedly.
The inherited Audit.lean additionally prints the original tree representation
for inherited declarations. The audit uses `value? (allowOpaque := true)`.
