# Statement correspondence for MathDB 365943

| Declaration | Exact role and hypotheses | Interface correspondence |
| --- | --- | --- |
| `filter_range_card` | For every natural order and Boolean predicate, the filtered range length equals the cardinality of the corresponding subtype of `Fin n`. | Bridges executable list counts to finite graph degrees. |
| `graphDegree_eq_delete` | Given the exact transported old adjacency specification, executable `graphDegree` equals the deletion graph degree at the permuted vertex. | No simple-code or coverage hypothesis is assumed. |
| `mask_length_eq_degree` | For every finite graph, deleted vertex and old permutation, the transported mask length equals the deleted vertex degree. | Includes every neighbor exactly once. |
| `deleteFin_degree_lt` | If the removed vertex is adjacent to an old vertex, deletion strictly reduces that old vertex degree. | The removed neighbor is outside the image of the injection on old neighbors. |
| `transportedMask_eligible` | For `0 < n`, connected `G` on `Fin (n+1)`, degrees at most 3, and a code representing the relabelled deletion, its transported mask is eligible. | Proves the nonempty, at-most-three, and selected-old-degree-less-than-three conditions literally used by the checker. |
| `catalogue_closed_1` through `catalogue_closed_7` | Each code in the actual source list has an inherited checked extension closure into the actual next target list. | Membership-indexed packaging of inherited certificates; no new finite enumeration assumption. |
| `covered_one`, `covered_step`, `covered_1` through `covered_8` | Every connected subcubic graph of each order 1 through 8 admits a permutation whose adjacency agrees with a listed code. | Deletion induction uses mask eligibility, the inherited exact extension specification, and the checked certificate permutation. |
| `coverage8 : Coverage8` | Every `Structural C s` admits `e : Equiv.Perm (Fin 8)` and `code ∈ GraphClosure7_000.targets` with `SupportCode (C.submatrix e e) code`. | Literal unchanged root-fixed Coverage8; uses inherited connectedness and degree bounds for `supportGraph`. |
| `nut8_target (hp : PerSupport) : Target` | Conditional full graph endpoint, compiled from the inherited byte-identical FinalEndpoint source. | Coverage8 is discharged; PerSupport remains an explicit argument. |

The source question is the nonexistence of cubic 8-circulant nut graphs, Bašić–Damnjanović arXiv:2411.16904, Conjecture 16, MathDB 365943. This lane completes the coverage bridge in the existing formalization. It makes no independent novelty or acceptance claim, and does not change the campaign count of 21/40 beyond 39.
