# Primary comparison for B8C

Myeongjin Kang; no affiliation. 2026-10-16. Prose CC BY 4.0.

| question | source family 156 (real, k = 4) | B8C (complex, k = 3) |
|---|---|---|
| set | X_4^R = {uu^T : u ∈ S^3} ⊂ R^9 | X = {uu^* : u ∈ S(C^3)} ⊂ R^8 |
| space it is homeomorphic to | RP^3 | CP^2 |
| linear-algebra lower bound | m ≥ N_4 = 10 (thm:label-bound) | m ≥ dim Herm_3 = 9 (Theorem A) |
| beyond the lower bound | ten labels impossible (thm:no-ten-labels), so b ≥ 11 > d + 1 | nine labels POSSIBLE (Corollary C), so b = 9 = d + 1 |
| conclusion | Borsuk fails in dimension 9 | X is not a Borsuk counterexample in dimension 8 |

## What carries over and what does not

- **Carries over:** the odd extension to all self-adjoint matrices and
  the Borsuk–Ulam count. The Hermitian version needs no new idea beyond
  replacing O(k) invariance with U(3) invariance (`∫uu^* dμ = I/3`).
- **Does not carry over:** the equality-case combinatorics. For RP^3 the
  source shows that the equality configuration (pure facets with k
  vertices, an F_2 facet cycle, all edges) cannot be realised with ten
  labels. For CP^2 the equality case is realised by an explicit cover.
  The obstruction is therefore genuinely real-specific at this size.

## Obstruction met and how it was resolved

The unperturbed Hesse SIC has covering value exactly 1/2 (Lemma 9). That
is the Bessel threshold, and every Voronoi cell has diameter exactly √2
because of the twelve MUB holes. A first-order analysis at a hole
(Lemma 11) shows that one trio of the six neighbouring SIC vectors must
gain overlap. The trio average matters, not single points. Each trio
lies on a Hesse line through two orthogonal holes, so a single motion
cannot help both poles.

The operation that resolves this: orient each of the twelve Hesse lines
cyclically inside its basis, so that each hole is favoured exactly once.
Then move the fiducial along a direction d_0 that is positive on all
four favoured poles of its four lines simultaneously. Lemma 10 shows
d_0 = (1 + i)(0, 1, 1)/2 does this. Weyl–Heisenberg covariance spreads
this to all nine points, because the orientation is shift-invariant.
The scope's warning ("a point cannot approach both members of an
orthogonal hole pair") is correct pointwise, but the cyclic orientation
never asks it to.

## Literature

Kalai's survey (1505.04952v1, Sections 2.3–2.6) records the real
projector embedding and the open question of the smallest failing
dimension. It does not mention complex projectors. A bounded web search
on 2026-10-16 found no statement of b(X) for the complex projector set
and no covering-radius statement for the Hesse SIC. This is an absence
of search hits, not a literature-novelty claim.
