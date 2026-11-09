# Statement correspondence

| Source or task requirement | Formal location | Status and limit |
|---|---|---|
| Source Section 2, graph representation | SourceContact.graphFunction, resolventMatrix | Actual inverse diagonal of adjacency minus color diagonal. All finite simple graphs, arbitrary root and Boolean coloring. No reciprocal normalization. |
| Reduced rational-inner representation | SourceContact.ReducedCertificate | Polynomial numerator and denominator; no common nonunit divisor; stable denominator; equality to beta composed with graph function on the bidisk; reflected denominator up to unit phase. Definition only; no certificate constructed for the candidate. |
| Bickel–Hong Section 3.1, local infimum definition | HasZeroSetContact, HasHalfPlaneContact | Copied with hash-bound original retained. Uniform lower bound over all local zeros and existence of a zero attaining an upper bound up to constants; no empty-infimum convention. |
| Source Conjecture 6.1 | SourceConjecture | Universal n, simple graph on Fin n, coloring, arbitrary root, reduced certificate, reachable nearest-w distance d and defined positive even local order K at (-1,1); asserts K = 2d. No connectedness, one-w or equal-branch hypothesis. |
| Bickel–Hong Remark 3.2 | Zero-set predicates | Infimum of distances selects the branch with the **maximum** vanishing order. Neither minimum order nor sum of branch orders is used. Generic level-set machinery is not claimed formalized. |
| Local square root via analytic inverse | QuadraticBranches.local_sqrt_one | Unconditional existence, analytic near 1, value 1, squared identity eventually. |
| L = -i normalization, x = -1/z, w = x u | A, B, C, D; analytic_exhaustive_branches | A = 1 - ix - 2x² + ix³, B = 4 - (2+2i)x - x², C = 3 - ix. D = (B² - 4AC)/4 has value 1. Two analytic roots with values -1 and -3, factorization and exhaustive normalized roots. The equivalence to the graph's matrix resolvent remains unproved. |
| Actual analytic remainder, order six | ExactOrders.concrete_analytic_remainder, concrete_order_six | Actual analytic root of normalized quadratic, analytic remainder, real-imaginary analyticOrderAt = 6. No polynomial-jet-only substitution for convergence. |
| Order two and full contact six | No final declaration | Missing; no full P3 endpoint. |
| Literal source refutation | No final declaration | Missing; no `¬ SourceConjecture`, no graph counterexample theorem. |

The source wording supplies no conventions for disconnected roots with no
reachable w vertex. NearestWDistance quantifies over walks, so the universal
assertion ranges over every case where that distance exists. Similarly, the
positive even order is quantified when the literal contact predicate holds.
This does not restrict the conjecture to the candidate graph. Relabeling
arbitrary finite vertex sets by Fin n gives the intended finite graph scope;
that relabeling equivalence has not been separately formalized. A connected
z-root graph with nonempty w set suffices to refute the universal statement,
but no such refutation is proved in this packet.

The square-root signs are chosen to produce u(0) = -1 and -3 in x = -1/z.
These negative slopes are consistent with the original positive slopes in
t = 1/z. No half-plane claim is inferred from the orientation-reversing
chart t = 1/z.
