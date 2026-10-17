S2 finite-family Lean support — implementation round 1
Myeongjin Kang (no affiliation). Original code and documentation: MIT.

This package supports the reviewed proof of two Seymour vertices in every
finite nonempty sink-free oriented graph. It DOES NOT formalize that theorem.
The full candidate is conditional on the stipulated ordinary Seymour theorem
and finite-relation pruning lemma at OpenAI math commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Neither is installed as a Lean axiom.
The supporting results here are unconditional elementary implications whose
hypotheses explicitly expose all missing graph and pruning facts.

COVERAGE

Eleven theorems in SeymourSupport.lean:
1–3 boundary_weak, boundary_strict, boundary_indicators: the integer consequence
of delta_D = delta_H + q + b - a, including all Boolean indicator cases. The
finite-graph-to-boundary identity is an INPUT and is not formalized here.
4 sum_with_specials: sum bound for arbitrary finite I and S subset I, with
f(i) <= n off S and f(i) <= n-m on S.
5 aggregate_bound: if |I| = nm, |S| >= m-1, m >= 0, the total is bounded by
n^2 m - m(m-1). The distinguished fibers need not be the only improved fibers.
6 aggregate_negative: choosing m=n^2+2 gives sum <= -m < 0. Integers are used,
so no truncating subtraction is hidden in these statements.
7–8 fiber_cardinality_strict, fiber_sigma_strict: negative sums of actual
finite-fiber cardinality defects imply strict cardinality inequalities, also
for disjoint tagged fibers represented as a sigma finite set. The connection
between graph coordinate images and these fiber families remains in prose.
9 complement_gain: genuine finite subsets of an ambient U, disjoint old
images, and two strict image cardinality inequalities imply the complement
cardinality gain. P and Q themselves are arbitrary finite sets; no unstated
containment is needed by this lemma.
10 pruning_objective_gain: if subsets of R,C delete at most d+d' elements,
and |R|+|C| > M+2d, their new objective is strictly greater than M+d.
11 complement_pruning_contradiction combines 9 and 10 with the explicitly
assumed maximal-objective inequality. It does not construct a pruning output.

NOT COVERED: existence/minimality of a counterexample; protected subset
deficits; the exact boundary identity from graph neighborhoods; strong
connectivity; transitive tournament image bounds; compatibility and anchor
exclusions; identification of coordinate images with tagged fibers; the
pruning theorem, its charge sets, diagonal retention, or output admissibility;
the full graph theorem; contribution/novelty or manuscript acceptance.

Seven theorem controls in Controls.lean give the general zero at m=n^2+1,
an actual ten-fiber zero example at n=2,m=5, a twelve-fiber zero example with
one missing anchor at n=2,m=6, a sharp -6 family with all five anchors, a zero
weak boundary deficit, an overlapping-image obstruction, and equality when
the pruning input gain is weakened to non-strict. These are counterexamples
to shortcuts, never counterexamples to the graph theorem.

BUILD FROM THE PORTABLE PROJECT

Pins: Lean 4.34.1, compiler commit 5045d0056413266e57c625dcd7c365b10e377c52;
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. lake-manifest.json pins every
transitive dependency. Install elan/Lean separately if unavailable. In this
directory, with network access for first dependency provisioning:

  lake exe cache get
  lake build

The supplied lean-toolchain selects the toolchain. The Lake manifest supplies
dependency revisions; do not replace it with an unpinned update. The cache
command fetches third-party compiled dependency objects. Original project
modules are compiled from the supplied source by lake build. Checks and
ControlChecks print exact types and axiom dependencies.

For a fresh isolated source build and machine-readable receipt, using that
portable dependency installation:

  python3 rebuild.py --lean /absolute/path/to/lean --cache .lake/packages
  python3 mutations.py --lean /absolute/path/to/lean --cache .lake/packages

The commands accept an optional --output relative/path-for-new-receipt.
Without flags, they reuse this repository's preexisting pinned cache and
compiler paths. Those defaults are conveniences, not portable dependencies;
always pass the paths explicitly outside this workspace. The dependency
cache is checked by git revisions and read only. Original sources are copied
to a newly created temporary directory; no prior support .olean is used.
The runner checks compiler identity, successful exits, absence of diagnostic
failure markers/warnings, all public declaration types, and each axiom list.
Only propext, Classical.choice and Quot.sound are allowed. Original theorem
sources contain no conclusion axiom, proof placeholder, native_decide or
unsafe declaration. This is an implementation receipt, NOT independent audit.

The four mutation runs compile temporary altered sources, expecting proof
failure: permit q=a-1 in the strict boundary lemma; reduce special count to
m-2; use m=n^2+1; weaken the pruning input gain to non-strict. Import/parser/
type-mismatch failures are rejected as invalid controls. Failed mutants are
not project sources and are not retained as .lean files. Their diagnostics
and content hashes are recorded. Controls.lean additionally proves concrete
counterexamples, so rejection is not merely failure of a chosen tactic.

  python3 semantic_checks.py
  python3 verify.py

The first runs bounded independent set/arithmetic calculations, with counts
in its JSON output. These checks are not a universal theorem or enumeration
of oriented graphs. verify.py checks only file identity against the sealed
manifest; it explicitly makes no mathematical certification claim.

RIGHTS AND PROVENANCE

SeymourSupport.lean, Controls.lean, queries, semantic_checks.py, mutations.py,
metadata and this README are original MIT material. checked_run.py and the
license text were copied from kn-minus-edge-formal-v1; rebuild.py was adapted
from that same repository-owned MIT implementation. Lean/mathlib and their
transitive packages are external dependencies under their respective upstream
licenses and are not vendored here. No third-party primary paper PDFs are
needed or bundled. The full candidate remains separate CC BY 4.0 prose.
See provenance.json, coverage.json, input-manifest.json, logs and the sealed
output-manifest.json. Public upload or acceptance is not claimed.
