# MathDB 364626 proof and certificate crosswalk

| Paper | Lean declaration or module | What the check establishes |
| --- | --- | --- |
| §1, distance-two adjacency and same-label iterates | [MetaBase](src/MetaBase.lean) · `metamour`, `meta_adj_iff_edist`, `phase`, `ExactPeriod` | Distinct nonadjacent vertices with a common neighbor are exactly the pairs at extended distance two. Iteration stays on the same type. Exact period includes equality and all smaller positive nonreturns. |
| §2, every phase connected and in the image | [MetaBase](src/MetaBase.lean) · `meta_reachable`, `phase_reachable`, `phase_preconnected`, `phase_predecessor` and [MetaScope](src/MetaScope.lean) · `phase_connected` | Reachability traces back from a sufficiently late multiple of the return time. The predecessor index also works for phase zero. Connectedness keeps nonemptiness on the same vertex type. |
| §2, short phase returns after two steps | [MetaBase](src/MetaBase.lean) · `meta_two_of_short`, `no_short_phase_of_odd_edge` and [MetaScope](src/MetaScope.lean) · `short_iff_ediam_le_two` | The predecessor supplies the common-neighbor witness in the complement. An odd return and a two-step return give a fixed phase, which cannot have an edge. |
| §3, two consecutive independent phases after a triangle | [MetaTriangle](src/MetaTriangle.lean) · `triangle_next_independent`, `triangle_obstruction` | Absence of a common metamour neighbor for each triangle pair implies the local two-neighbor property. The proof uses walk induction to propagate that property. The final explicit pair cases find a common neighbor. |
| §4, history excludes nonzero monochromatic triangles | [MetaTriangle](src/MetaTriangle.lean) · `equal_history_no_triangle` and [MetaDegree](src/MetaDegree.lean) · `history`, `history_symm`, `phase_mod`, `history_eq_adj` | Word equality implies the same state at all times, including across the wraparound. A triangle propagates by two phases and eventually contradicts the immediately following independent triple. |
| §4, finite Ramsey and degree | [MetaRamsey](src/MetaRamsey.lean) · `triangleBound`, `ramsey_triangle` and [MetaDegree](src/MetaDegree.lean) · `degreeBound`, `odd_return_degree_bound` | Lean uses ordered arguments to the color function and proves the needed equalities in one triangle ordering. The application has symmetric colors. The finite pigeonhole proof removes the pivot color when it cannot close a triangle. For a pair of neighbors, phase zero or one supplies a nonzero color. |
| §5, geodesic and diameter | [MetaDiameter](src/MetaDiameter.lean) · `dist_le_add`, `geodesic_split`, `edge_dist_le_pow`, `edge_of_dyadic_dist`, `return_diameter_bound` | Walk prefixes and suffixes achieve the exact split distances by the triangle inequality. The distance upper bound rules out an edge one phase too early. Positive return forces distance strictly less than the dyadic threshold. |
| §5, ball and order | [MetaOrder](src/MetaOrder.lean) · `ball`, `mem_ball_of_walk`, `ballBound`, `ball_card_bound`, `odd_return_order_bound` | The recursively constructed finsets contain every vertex reachable within the stated radius, and a union bound proves the recurrence. The geometric sum in the paper follows from the recurrence. The empty case is separate in Lean. |
| §6, finite representatives | [MetaFiniteness](src/MetaFiniteness.lean) · `metamour_comap`, `phase_comap`, `comap_injective`, `exactPeriod_iso_iff`, `finite_exact_odd_period`, `finite_exact_odd_period_preconnected` | Transport of graph relations is injective along a bijection and commutes with all phases. A finite sigma type enumerates all graphs on bounded `Fin n`, then filters for connectedness and least positive period. Its representatives give an isomorphism cover. |
| §6, small cases | [MetaScope](src/MetaScope.lean) · `exactPeriod_one_iff_subsingleton`, `exactPeriod_subsingleton_iff` | Exact period one in the preconnected convention is equivalent to a subsingleton vertex type. The period-three classification is native Theorem 7.5 and is outside the replay dependencies. |
| §1 and §6, expanded native endpoint | [ReviewNativeEndpoint](src/ReviewNativeEndpoint.lean) · `distanceTwo`, `iterateDistanceTwo`, `finite_native_least_labeled_odd_return` | Review-only module states actual extended-distance adjacency and explicit odd witness, positivity, labeled equality and smaller nonreturns on both the input and every representative. The `#check` and standard-axiom report are in formal attempt 17. |

## Reproduction and artifacts

Start in a clean working copy with the supplied lane helpers, pinned binaries and libraries, and immediately empty `src/`, `build/`, and `cache/`. The extractor parses the frozen source appendix and cross-checks the owned canonical text and declared digests. The delivered [appendix](LEAN-SOURCE-APPENDIX.md) is byte-for-byte the same file, and [SOURCE-MAP.json](SOURCE-MAP.json) gives the half-open byte offsets of the eight module bodies. Do the compile and separate kernel check in this order, waiting for both to succeed at each step.

1. MetaBase
2. MetaTriangle
3. MetaRamsey
4. MetaDegree
5. MetaDiameter
6. MetaOrder
7. MetaFiniteness
8. MetaScope

Use `taskset -c 0,1 bash check32.sh MODULE UNIQUE_COMPILE_LABEL` and `taskset -c 0,1 bash checker32.sh MODULE UNIQUE_CHECK_LABEL`. The optional review-only module follows MetaScope and lives separately from the canonical appendix. The version print runs as part of MetaBase. [FORMAL-MAP.tsv](FORMAL-MAP.tsv), [DEPENDENCY-MAP.tsv](DEPENDENCY-MAP.tsv) and [AXIOM-MAP.tsv](AXIOM-MAP.tsv) identify each receipt, direct import, physical olean, and dependency-axiom output.

The crosswalk checks assembly of this manuscript against the personally audited proofs and replay. This lane wrote the manuscript and its crosswalk. A separate reader has yet to review the finished manuscript itself.
