# Statement correspondence

The frozen interface is byte-identical to r3b and r2. This lane does not
reinterpret the graph statement or modify Part A. The inherited source mapping
is preserved in `inputs/nut-formal-r3b/statement-correspondence.md`.

| Requirement | Declaration | Exact scope |
| --- | --- | --- |
| Required Part B endpoint | `Nut8.finite_obstruction` | Absent |
| Frozen finite statement | `Nut8.FiniteObstruction` | `∀ C ε s, Admissible C ε s → ¬ (C.det = 0 ∧ ∀ i, C.adjugate i i ≠ 0)` |
| Structural support | `supportGraph` | SimpleGraph on `Fin 8`; adjacency is `i ≠ j ∧ C i j ≠ 0` |
| Connected support | `supportGraph_connected` | Every `Structural C s` |
| Subcubic support | `supportGraph_degree_le` | Every vertex; degree at most three |
| Removable vertex | `connected_removable_vertex` | Connected graph on `Fin (k+2)`; induced complement remains connected |
| Standard finite deletion | `deleteFinIso` | `deleteFin G v ≃g G.induce {v}ᶜ` |
| Inductive hypothesis preservation | `connected_subcubic_deleteFin` | Connected, degree at most three on `Fin (k+2)` yields such deletion on `Fin (k+1)` |
| Checked list to permutation | `checkedEquiv` | Any list permutation of `List.range n` |
| Checked bits to graph isomorphism | `graphIsoCheck_equiv` | Successful checker plus explicit adjacency specifications for the two graphs |
| Checked closure to graph isomorphism | `extensionClosed_equiv` | Successful closure, eligible bounded mask, and adjacency specifications; some listed graph is isomorphic to that extension |
| Universal catalogue coverage | None | Induction and encoding proofs still missing |
| Final MathDB statement | `Nut8.Target` | Unchanged and no inhabitant produced here |

All new declarations use only ordinary kernel-checked Lean proofs. No novelty or
prior-art clearance is claimed; root alone decides acceptance.
