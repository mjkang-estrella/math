# Feasible, deliberately scoped Lean support

No Lean file or full formalization is claimed in this discovery packet. The campaign's existing toolchain is Lean 4.34.1 with mathlib pinned at d13f23b723b8a846827a245b89c10fc7d3f11612. A later isolated support package can use those exact dependencies without editing the shared formal project.

The following interfaces are feasible and mathematically relevant:

1. For a finite nonempty index set, integers d_j≥i≥2 and Σ(d_j−i)≤1 imply d_j≤i+1<2i. A companion proves the sum conversion from Σ(d_j−1)≤r(i−1)+1, with r the actual finite cardinality. These support the strict no-splitting cutoff, including i=2.
2. For integer dimensions n≥2, b≥0, a support dimension z≥2n−1 and z≤max(2n−b,2n−2) imply b≤1. Integers avoid natural-number truncation hiding a boundary case.
3. For a binary relation R on a type X and a subset U saturated under R, prove the exact relation inclusion R⊂(R restricted to U×U)∪((X\U)×(X\U)). With a supplied map constant on related points of U, refine the first piece to the fiber relation. This is a genuine set-theoretic part of the two-endpoint argument, not an assumption of the final conclusion.
4. If every generating curve relation preserves a subset F, its reflexive transitive chain closure preserves F. Together with a nonempty proper F this contradicts universal chain connectedness. This supports the horizontal-selection contradiction after the geometric family contracts have been supplied.
5. A linear functional on a finite-dimensional vector space which vanishes on a spanning set is zero. A supplied nonzero value therefore contradicts its vanishing on each representative class. This supports the divisor contradiction while leaving numerical intersection theory external.
6. Picard-number induction arithmetic: n≥r(i−1), r≥2, i≥2 give n−i+1>0; if j≥i and r(i−1)≥n−1, then (r−1)(j−1)≥(n−i+1)−1. A second lemma isolates the possible increase j>i under the base Mukai bound.

No proposed declaration assumes the advanced Mukai classification or packages it under a renamed axiom. The support intentionally does not define Fano manifolds, RatCurves, Chow groups, virtual cycles, refined intersections, proper rational-chain quotients, numerical divisor spaces, projective bundles, or Mori contractions. In particular, formalizing item 3 does not verify that the geometric quotient has the stated saturation property. Those remain exact human mathematical obligations in proof.md and the cited primary inputs.

Suggested independent semantic controls: break saturation and exhibit a mixed U/complement related pair; replace 2n−2 by 2n−1 and show b=2 is no longer excluded; set i=1 and show i+1<2i fails; drop the span premise from item 5; allow degree 2i in item 1; reverse the inequality for the base pseudoindex. An eventual Lean audit should check these controls and standard axioms, not merely compilation.
