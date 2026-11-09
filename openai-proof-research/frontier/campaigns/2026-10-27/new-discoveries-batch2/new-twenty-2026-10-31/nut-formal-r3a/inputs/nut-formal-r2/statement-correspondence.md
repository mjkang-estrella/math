# Exact statement correspondence

| Requirement | Declaration / artifact | Scope |
| --- | --- | --- |
| Original cubic, nut and 8-circulant endpoint | inherited `Nut8.Target` | Byte-identical definition; no inhabitant |
| A1 global coordinates | `Nut8.nut_circulant_global_coordinates` | From the actual inherited Nut and Circulant predicates; V ≃ Fin 8 × ZMod m, m > 0, generator acts by +1 |
| Periodic representative independence | `Nut8.character_natCast`, `character_add` | Integer epsilon, epsilon^m = 1, m nonzero |
| Signed quotient definition | `Nut8.signedQuotient` | Actual simple graph on labelled vertices; integer epsilon^b.val |
| Quotient symmetry | `Nut8.signedQuotient_symmetric` | Assumes labelled adjacency translation invariance and periodic sign |
| Restriction solves quotient kernel | `Nut8.signedQuotient_kernel` | Assumes actual graph kernel and explicit coordinate character identity |
| A2 injective lift and nullity | None | Missing |
| A3 decidable grammar | `Nut8.Admissible` | Coherent signs after double-edge cancellation exclusion; graph extraction unproved |
| Unsigned quotient | `Nut8.unsignedQuotient`, `unsigned_row_sum`, `trivial_character_unsigned` | Absolute-entry definition and epsilon = 1 specialization; equality to actual graph quotient unproved |
| Verified executable determinant | `Nut8.sparseDet_eq_det` | Every natural dimension and integer matrix |
| Verified principal cofactor | `Nut8.sparseDet_principal` | Every nonempty finite integer matrix and diagonal position |
| Rank-one adjugate implication | None | Missing |
| Explicit finite proposition | `Nut8.FiniteObstruction` | Definition only; no proof and no bridge to Target |
| A5 conditional endpoint | None | Missing |
| B concrete matrix checks | `Nut8.Pilot.certificate0`, `certificate1`; `Nut8.HardDet.certificate`; `Nut8.HardCofactor.certificate` | Four actual determinant/cofactor equalities; not universal enumeration |
| B normal-form completeness | None | Missing |

No primary-source or prior-art gate was repeated. Source and prior-art inputs are
hash-identical copies of the assigned r1 packet. No claim of solving MathDB
365943 or of new-to-literature novelty is made.
