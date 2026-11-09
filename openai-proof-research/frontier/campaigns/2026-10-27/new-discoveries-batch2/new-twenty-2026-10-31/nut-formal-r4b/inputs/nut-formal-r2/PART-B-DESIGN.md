# Finite obstruction design and measurements

The finite grammar is explicit in `formal/FiniteGrammar.lean`. `SupportConnected`
quantifies over the 256 vertex subsets and requires a nonzero crossing entry for
every nonempty proper cut. Entries have magnitude at most two, rows have absolute
sum three, and diagonals are 0, ±2, or the shared semi-edge sign s. Epsilon and s
are signs. The epsilon = 1 branch is nonnegative. This is a coherent signed
contribution grammar, pending its derivation from graphs.

## A smaller proof dependency graph

Use all structural signings, with no unsigned-kernel pretest. The new exact
integer experiment `scripts/check_grammar.py` reports:

- 194 connected subcubic underlying catalogue graphs;
- 669 distinct augmented matrices in the chosen catalogue labellings;
- 9,172 distinct positive-tree normalized signed matrices after imposing the
  shared semi-edge sign, including both choices of that sign;
- 8,208 nonzero determinants;
- 964 zero determinants, each with a zero principal cofactor;
- zero survivors.

These are exact counts of this Python generator's outputs. They are not counts
of all labelled admissible matrices, isomorphism classes of augmented matrices,
or formally proved BFS-normal forms. `all-normalized-certificates.json` records
all 9,172 integer witnesses. The generator uses Bareiss elimination with exact
division checks and scans all eight principal minors on singular cases. There
is no floating-point inference or external package. This diagnostic computation
is not a trusted proof ingredient.

The inherited pretest reduced the certificate set to 7,176. Checking 1,996 extra
matrices removes the unsigned spectral-pretest proof obligation from the finite
search. This does not remove the main signed quotient bridge.

## Required normal form

A complete route is to formalize connected graph augmentation through eight
vertices: delete a spanning-tree leaf, enumerate all one-, two-, and three-element
neighbor subsets, and canonicalize by a minimum over the finite permutation group.
Prove canonicalization is a relabelling and is invariant under relabelling.
Prove by induction that every connected subcubic graph is represented. Then
augment ordinary edges to multiplicity two and fill residual degrees with a
single loop or semi-edge, proving completeness from the row sums. Fix a spanning
tree and recursively switch vertices to make its edges positive. Prove that
switching preserves determinant zero and zero/nonzero diagonal cofactors.
The sign-free grammar and shared diagonal sign are preserved. Epsilon = 1
positivity need not be preserved: normalize in the larger epsilon = -1 grammar,
which contains the structural cases of both characters. This avoids a false
unrestricted switching-invariance claim.

The cached 194-graph catalogue can be used as a comparison oracle during
implementation, but cannot serve as an assumed exhaustive list. An alternative
is a verified BFS generator; no BFS output count or completeness theorem has
been obtained here. No normal-form theorem is claimed.

## Kernel computation

`VerifiedDet.sparseDet` recurses on the dimension-indexed integer matrix. A zero
first-row entry returns zero without evaluating the recursive minor. Induction
using mathlib's row-zero Laplace theorem proves equality with `Matrix.det` for
all dimensions. `sparseDet_principal` proves equality with each actual principal
adjugate entry. The definition is noncomputable to avoid generating partial
executable code; it remains kernel-reducible. All pilot computations use
`decide +kernel` after rewriting by these correctness theorems.

`DetPilot` proves one actual determinant is 48 and one actual cofactor is zero.
`HardDet` and `HardCofactor` select the largest recursive expansion trees among
the inherited 7,176 certificate choices (375 and 118 nodes respectively).
This selection is NOT a hardest-case claim for the larger 9,172 set or for
arbitrary admissible matrices. `pilot-selection.json` records exact selections.

Initial measured whole-process compilation costs, including Lean startup:

| Module | Wall seconds | Sampled private bytes |
| --- | ---: | ---: |
| DetPilot (two certificates) | 2.292 | 1,623,371,776 |
| HardDet | 1.750 | 2,460,385,280 |
| HardCofactor | 1.265 | 2,355,458,048 |

Memory observations vary with startup/page sharing and are not hard bounds.
Fresh replay measurements are authoritative receipts in `fresh-extracted/logs`
(or the final fresh replay directory named in SUMMARY.md). Every Lean and
leanchecker call has the 6 GiB private-memory watchdog, two-CPU affinity,
120-second CPU limit, and 140-second wall limit. There is one heavy child at a
time and `MALLOC_ARENA_MAX=2`.

At roughly one to two seconds per separately compiled certificate, a naive
9,172-module replay suggests about 2.5 to 5 hours, mostly startup overhead.
This is a planning estimate, not a measured total or verified upper bound.
Bundling should be measured under the memory cap rather than extrapolating
linear memory use. Four new Lean certificates are supplied; the remaining
9,168 catalogue certificates and the formal coverage theorem are not supplied.
