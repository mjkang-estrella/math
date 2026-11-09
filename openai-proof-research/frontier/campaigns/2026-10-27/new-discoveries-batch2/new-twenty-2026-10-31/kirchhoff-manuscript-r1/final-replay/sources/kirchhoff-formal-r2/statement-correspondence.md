# Statement correspondence

| Source or binding ruling | Lean object and justification |
| --- | --- |
| Finite simple graphs, at least two vertices | `Kirchhoff.Graph n`, Boolean adjacency with symmetry and no loops; `Graph.simple` is a mathlib `SimpleGraph (Fin n)`; both conjectures quantify over every `n ≥ 2` and every connected such graph. Boolean adjacency loses no finite decidable graph. |
| Degree and K to the power alpha | `degree` sums adjacency indicators; `Kpow` is diagonal with integer powers of the rational degree. |
| Equation (3.8) | `laplacian`; `laplacian_source_formula` proves it equals diagonal row weights minus `Kpow g a * adjacency g * Kpow g (-a)`. All integer alpha values are defined; the conjectures restrict alpha to 1 or -1. Real entries are the exact scalar extension of these rational entries. |
| Moore–Penrose pseudoinverse | `Penrose` contains all four equations, including both transpose equations. `penrose_unique` proves uniqueness over Q, and `KirchhoffReal.penrose_unique` over R. `validMPZero` and `validMPOne` exhibit existence at the witness; `lift_penrose` transfers every equation to R. |
| Equation (4.3), primary | `pairIndex` sums `Xii + Xjj - Xij - Xji` over `i < j`. `resistance_sum` also identifies the sum of the graph-level `resistance`. Neither inverse is assumed symmetric. |
| Definition 4.5 | `indexMP` is the sum from (4.3). `LiteralConjecture` also states the source directly with existential inverse data, removing any dependence on choice defaults. The existential data are unique by the proved uniqueness theorem. |
| Lemma 4.6, secondary | `GroupInverse` contains AXA=A, XAX=X, AX=XA; `group_unique` proves uniqueness over Q and R. `spectralIndex` is n times the trace of that unique group inverse, as permitted by the binding ruling. No unproved eigenvalue bridge is used. |
| Conjecture 4.13 | `KirchhoffReal.LiteralConjecture` states universal ordering for alpha in {1,-1} and equality iff regular, with existence of the inverses explicit. `KirchhoffReal.refuteMP` and `.refuteSpec` negate the two readings. Rational counterparts and choice-based index formulations are also proved false. |
| Witness | `witness` is K6 on 0 through 5, with edges 0–6–7–8–9–10. `witness_connected`, `witness_degrees`, `lapZero`, and `lapOne` establish the graph-to-certificate bridge. |
| Physical Definition 4.1 | Not the endpoint. The binding ruling finds the all-pairs potential interpretation ill-posed on nonregular graphs. We use the two algebraic readings exactly as ruled, without asserting equivalence to that physical definition. |

The existential formulations do not assume a global inverse existence theorem. They state existence as part of the universal source assertion and refute its ordering at a graph where existence and uniqueness are both proved. The auxiliary `mp`/`gi` selectors have a zero default outside their existence predicates; the primary real endpoints do not depend on these selectors or their defaults.
