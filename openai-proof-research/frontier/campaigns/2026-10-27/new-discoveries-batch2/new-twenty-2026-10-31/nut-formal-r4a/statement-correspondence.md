# Statement correspondence for MathDB 365943

The primary-source correspondence and source scope are inherited without change in `inputs/nut-formal-r3a/statement-correspondence.md`. This lane adds the previously missing Part A bridge, not a new mathematical problem or a novelty claim.

| Obligation | Literal declaration | Connection |
| --- | --- | --- |
| Original graph predicate | `Nut8.Target` (unchanged Nut.lean) | Every finite decidable simple graph fails the conjunction Cubic, Nut, Circulant 8. |
| Degree transport | `coordinateGraph_cubic` | Pullback through the actual equivalence L preserves degree three. |
| No signed cancellation | `abs_signedQuotient_eq_card` | Each absolute entry equals its actual graph neighbor fiber cardinality. |
| Frozen unsigned quotient | `unsignedQuotient_actual` | Function equality with the actual neighbor-count matrix. |
| Absolute row sum | `signedQuotient_abs_row` | Each row sums to three. |
| Support cuts | `signedQuotient_supportConnected` | Nut cuts in the original graph yield nonzero crossing quotient entries. |
| Entry bound | `connected_cubic_entry_bound` | Symmetry, absolute row sum three, and connected support on eight vertices imply magnitude at most two. |
| Diagonal | `signedQuotient_diagonal` | Each diagonal is 0, 2, -2 or ε^(m/2). |
| Trivial character | `signedQuotient_nonneg` | ε = 1 makes every entry nonnegative. |
| Small orbits | `diagonal_m_one`, `diagonal_m_two` | Internal contributions for m = 1 and m = 2 are explicitly computed. |
| Complete graph grammar | `coordinate_signedQuotient_admissible` | Every field holds on the same graph-specific signed quotient with s = ε^(m/2). |
| Algebraic signature | `integer_full_kernel_det_adjugate` (unchanged) | Real nullity one and full kernel imply integer determinant zero and all diagonal cofactors nonzero. |
| Requested endpoint | `endpoint_of_finite` | `Nut8.FiniteObstruction → Nut8.Target`, with no bridge assumptions. |

Circulant is the inherited equal-orbit cyclic automorphism predicate; its equivalence with the cyclic-subgroup formulation is the unchanged CyclicBridge theorem. FiniteObstruction is assumed only as the theorem's explicit argument. No conditional intermediate theorem is substituted for an unconditional resolution of MathDB 365943.
