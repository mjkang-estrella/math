# Family120: the compatible factor reduction is already available

This is pre-freeze feasibility and reduction analysis, not a nominee or a gate classification.

## Exact screened contract

The plausible lead was feasibility and explicit construction for a finite simple unweighted graph G with, independently at every vertex v, an interval of permitted degrees `[g_v,h_v]` or a parity interval `{g_v,g_v+2,...,h_v}`, where `0<=g_v<=h_v<=deg_G(v)` and parity endpoints agree. Input uses adjacency lists and one-word endpoints. The hoped-for cost was one uniform randomized `(n+m)^(1+o(1))` word algorithm, with an every-execution clock, valid outputs on success, and success probability at least 2/3 whenever feasible. No weighted optimization or binary multiplicities are included in this screen.

Source120's `thm:main` has the required uniform cardinality algorithm and every-path cost. `cor:f-factor` and the complete `factor:reduction` proof already handle arbitrary exact degrees via `uniform:network`, not by a quadratic complete bipartite gadget. These actual lower proof operations must be used before claiming the interval or parity interfaces unpaid.

## Network compatibility calculation

Retain the source's two incidence ports for every host edge, joined by a cross edge. At a degree-d vertex use its split acyclic permutation network, with d assigned input positions. A chosen cross edge represents a selected host edge. Every port and split network endpoint is required to be covered. Network transitions and idle edges are exactly those in `factor:reduction`.

For a parity interval `{g,g+2,...,h}`, attach `d-h` mandatory sinks to distinct outputs. Attach a further `h-g` sinks, partitioned into pairs, to other distinct outputs; connect the two sinks in each pair by one edge. Every sink is required. A pair either uses its internal edge or has both sinks matched to the network. Hence the number b of network output attachments lies in `{d-h,d-h+2,...,d-g}`. The source input/output cancellation gives precisely b absorbed ports and `d-b` selected cross ports.

Conversely, for any permitted host degree and any specified subset of its selected incidences, the complementary b inputs can be routed to the mandatory sinks and any `(b-(d-h))/2` sink pairs. Extend that partial input/output bijection to a permutation and apply the **existing** vertex-disjoint routing lemma. Pair unused paired sinks internally and idle every unused network position. There is no new disjoint-routing assertion.

For an ordinary interval `[g,h]`, use `d-h` mandatory sinks and `h-g` optional individual sinks. Each optional sink may remain unmatched. The same cancellation permits exactly every integer b between `d-h` and `d-g`. Again, any such choice routes by the same permutation network. All other vertices are required.

Required-vertex matching reduces to ordinary perfect matching with only a factor-two expansion: take two disjoint copies of the constructed graph and join corresponding optional vertices. A matching covering every required vertex extends by its identical copy and cross-copy edges on uncovered optional vertices. Conversely, restriction of a perfect matching to the first copy covers all its required vertices; only optional vertices can have used cross-copy edges. This establishes both directions, rather than assuming an ordinary maximum matching automatically prioritizes required vertices.

The number of positions, edges, and records is `O(n+m log(n+2))`. All identifiers have `O(log(n+2))` bits. Zero-degree vertices have no local gadget and require degree zero. One call to the source algorithm on the doubled simple graph, followed by a perfect-coverage check and the cross-edge decoder, suffices. There is no repeated randomized oracle whose success probabilities accumulate. The source's logarithmic expansion and physical-word simulation already absorb this size change in its common exponent envelope. Invalid outputs are rejected; infeasible inputs cannot be accepted after checking.

This calculation identifies a complete compatible reduction for the screened feasibility interface. It is not a new mechanism justified by a stronger-looking theorem statement. The full weighting problem in r35 remains different.

## Strongest primary comparison and the genuinely different boundary

Shao–Živný, *A Strongly Polynomial-Time Algorithm for Weighted General Factors with Three Feasible Degrees*, ISAAC2023 author proceedings PDF, AppendixA, Definition18, Lemma19 and Theorem20, explicitly treats matching gadgets with optional and required internal vertices. Its interval construction is printed and its parity construction is credited to Cornuéjols. The source network pays the potentially expensive all-to-all routing part of those gadgets; it is not legitimate to ignore that source operation and nominate sparsification alone.

The same primary proves that allowed degree sets with gaps at most one are matching-realizable exactly when they are intervals or parity intervals. For the smallest obstruction `{0,1,3}` on three ports, compare realizing matchings for all three ports and no ports. Their symmetric difference decomposes into alternating components. Required internal vertices are covered by both matchings, so they cannot be path endpoints. The changed ports are partitioned into components containing one or two ports. Three ports force a singleton component; toggling it from the all-three matching yields exactly two covered ports while preserving all required internal coverage. Degree two is forbidden. This is the existing primary obstruction, not a new result.

Thus broader degree sets cannot be handled by merely adding new optional sink patterns. A nonlocal reduction or a new algorithm is not ruled out. The primary's recursive parity-fixing algorithm and local-search structural lemma go beyond matching gadgets, but no near-linear bound for that recursion was obtained here. This is why no broad general-factor target was frozen.

The r35 weighted-contraction example (optimum6W versus2W under two odd-bin contractions) and r109's actual screen were read. No signed-weight, scaling, degree-parameter, or exact-f-factor variant is renominated.

Primary body: https://www.cs.ox.ac.uk/standa.zivny/publications/sz23isaac-preprint.pdf . Exact pinned source paths, labels, raw URLs and authenticated blobs are in `private/upstream-manifest.json`.
