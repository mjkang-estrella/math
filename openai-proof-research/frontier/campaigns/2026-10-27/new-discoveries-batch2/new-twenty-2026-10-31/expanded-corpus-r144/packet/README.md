# Internal candidate 346167

Run ./verify.sh from this directory. The scripts use Lean 4.34.1 and the
read-only cached mathlib dependencies designated in TASK.txt (pin
d13f23b723b8a846827a245b89c10fc7d3f11612). No upstream rebuild or independent
cache validation is claimed. Every numerical/Lean/checker invocation uses
scripts/run: two CPUs, 120 CPU seconds, 140 wall seconds, 6 GiB sampled
aggregate RSS watchdog, MALLOC_ARENA_MAX=2; Lean also has -M3500.

The main endpoint is Rainbow.mathdb_346167_literal in Semantics.lean.
Base contains the graph, unbounded walk/cut semantics and soundness theorem.
The sixteen C?R? modules contain separately evaluated finite certificates;
Certificates assembles them. Final proves connectivity and the contradiction.
Semantics proves the exact rainbow-extension and minimum-number bridges.
Audit audits transitive axioms of every one of the 168 local declarations.

Only source files and reproducible scripts are packaged. There are no
precompiled local modules in the archive. This is not self-accepted work.
