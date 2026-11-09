# Statement correspondence

| Source statement or component | Lean declaration | Role |
| --- | --- | --- |
| MathDB 365943, Bašić–Damnjanović arXiv:2411.16904, Conjecture 16: no cubic 8-circulant nut graph | Nut8.no_cubic_8circulant_nut : Nut8.Target | Newly assembled literal endpoint; validation status is recorded separately in results.json. |
| Every finite vertex type and simple graph, not (Cubic G and Nut G and Circulant 8 G) | Nut8.Target in Nut.lean | Inherited endpoint definition with all original graph definitions. |
| Structural quotient support covered by catalogue | Nut8.coverage8 | r6p bridge. |
| All catalogue supports obstruct a full one-dimensional kernel | Nut8.per_support : Nut8.PerSupport | r6q finite certificate assembly. |
| Coverage and support obstructions imply finite obstruction | Nut8.finite_of_parts | r6p bridge. |
| Finite obstruction implies literal target | Nut8.endpoint_of_finite | Inherited r4a chain in r6p. |
| Conditional assembly | Nut8.nut8_target (hp : PerSupport) : Target | r6p conditional theorem, supplied with r6q per_support by Nut8Final. |

The new endpoint is `nut8_target per_support`, with no residual hypotheses in its declared type. Compilation, leanchecker and audit completion must be checked in the replay receipts; source assembly alone is not a validated result. Prior source correspondence is preserved in inputs/nut-formal-r6p and inputs/nut-formal-r6q. No novelty, acceptance or count credit is asserted here.
