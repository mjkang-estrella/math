# I248: uniform rooted-pattern packing amplification

2026-10-12. Author-level proof; not independently reviewed. Candidate for separate proof and contribution gates, not an accepted finding. All pinned OpenAI results are stipulated true. No research code, experiments, numerical scans, subordinate agents, staging, commits, or public communications were used.

## 1. Exact result and definitions

Fix an integer d≥2. There is N_d such that the following holds for n≥N_d, an integer 1≤s≤10 log n, and 0<r<1 satisfying

    b = ds + binom(d,2),       r^b ≥ n^(-1/100).

Put L=64d and p=1−(1−r)^(2L)≤128dr. There are deterministic classes D=D(n,r,s,d) and E=E(n,r,s,d) of labelled graphs on [n] with

    P(G(n,r)∈D) ≥ 1−ε_d(n),     P(G(n,p)∈E) ≥ 1−ε_d(n),

where ε_d(n)→0 uniformly over the allowed r,s, with this property.

For EVERY G∈D, EVERY H∈E, EVERY Y⊆[n] of size at most n^(2/3), and EVERY family R of rooted d-vertex patterns as defined next, writing N=n−|Y| and a_Y=floor(N/(16d²)),

    ν_R(H;Y) ≥ min{2d ν_R(G;Y), a_Y}.                 (T)

A labelled rooted pattern is (A_1,…,A_d,F), where A_i⊆Y, |A_i|≤s, and F is any simple graph on [d]. A d-element subset U of [n]−Y is compatible if it admits an ordering u_1,…,u_d and a pattern in R such that all edges u_i y (y∈A_i) and all u_i u_j (ij∈E(F)) are present. Extra edges are allowed. ν_R is the maximum number of pairwise vertex-disjoint compatible d-subsets. Thus the roots can be reused without limit, whereas the nonroots cannot. We may close R under all permutations of its d slots without changing ν_R. R is finite automatically; it can be empty, contain repeated-neighborhood types, or contain a pattern with no required edges.

The quantifiers in (T) concern a Cartesian product D×E. They do not require a coupling between the two hosts, a predetermined R, bounded degrees at roots, or disjoint root neighborhoods. The cap a_Y is essential. No induced/nonedge constraints, prescribed nonroot candidate lists, unbounded d, or optimal density is asserted.

## 2. Source operation and genuinely additional step

The pinned graph-decomposition manuscript, `Graph-Decompositions-at-the-Integral-Expectation-Threshold-October-5-2026/build/main.tex`, proves `lem:compression` and `prop:transfer`. Its compression applies to arbitrary families of sets of size ≤s under independent Bernoulli extension. Its transfer uses scalar sums of smoothed one-vertex tests and ordinary Hall matching, with the roots fixed. Those statements and their full proofs were read.

Below, the same compression operation is applied to the entire edge requirement of a d-vertex block. Scalar candidate counts are replaced by maximum weighted vertex-disjoint packing, and Jensen's inequality relates that functional to smoothed packing rank. The additional packing amplification in §5 uses exchangeability plus independent graph layers. This is the proposed new bridge; compression, bounded differences, sprinkling, and the classical matching theorem are credited inputs/techniques, not claimed individually as discoveries.

## 3. Compression, symmetrization, and a packing functional

For completeness, the precise bounded-support form of the pinned compression argument is paid here. Let Ω be a finite coordinate set, and let R be a nonempty family of subsets of Ω of cardinality at most b. Start with Q empty. While some T∈R has

    P(Z contains a member of Q | T⊆Z) < 1/2,     Z∼Bernoulli(r)^Ω,

add T to Q. Each addition increases P(Z contains a member of Q) by more than r^|T|/2≥r^b/2. Thus fewer than 2r^(−b) additions occur. At termination, for every S containing a member of R,

    P(S∪Z contains a member of Q) ≥ 1/2.          (1)

The conditional product law is exactly T∪Z; monotonicity extends the assertion from T to S. The empty support, if present, causes no problem: its conditional event is well-defined and it can be selected once. This proves the form needed here without invoking an undocumented extension of the source.

For fixed Y, the local coordinate space is the d|Y| root incidences together with the binom(d,2) internal possible edges. A pattern has at most b required coordinates. Apply (1) to the permutation-closed R, then close Q under permutations. Its cardinality is at most

    M = d! ceil(2r^(−b)).

Its members still belong to R. Define w_Q(U;G) to be the probability that U becomes Q-compatible after adding independent Bernoulli-r edges to its local coordinates. Slot symmetrization makes this independent of the ordering of U. Define

    W_Q(G;Y) = max_M sum_{U∈M} w_Q(U;G),

where M ranges over vertex-disjoint collections of d-subsets of [n]−Y. For every R-packing in G, (1) gives weight at least 1/2 for each block. Consequently

    ν_R(G;Y) ≤ 2 W_Q(G;Y).                       (2)

Let τ=1−(1−r)² and μ_Q=E ν_Q(G(n,τ);Y). Adding an independent whole Bernoulli-r graph to G(n,r) produces G(n,τ). Conditional on G, any fixed matching M satisfies

    sum_{U∈M} w_Q(U;G)
      = E[ number of Q-compatible members of M after addition | G ]
      ≤ E[ν_Q(G∪G';Y) | G].

Maximize on the left and average to obtain

    E W_Q(G(n,r);Y) ≤ μ_Q.                       (3)

Crucially, the maximum is outside the conditional expectation only on the left. This direction of Jensen is correct. No independence between the smoothed compatibility events of different candidate blocks is assumed.

## 4. Uniform concentration and counting tests

Partition the random coordinates used here into N independent blocks indexed by v∈[n]−Y: block v contains all edges from v to Y and all outside edges vw for which v precedes w in a fixed order. Edges within Y are irrelevant. Resampling block v only changes compatibility or weight of d-subsets containing v. Any matching contains at most one such subset. Dropping that subset from an optimum on either side shows that both ν_Q and W_Q change by at most one. Their values lie between 0 and floor(N/d).

The independent-block bounded-differences inequality therefore gives, for either functional Z,

    P(|Z−EZ|≥t) ≤ 2 exp(−2t²/N).                (4)

Only its one-sided version is needed. This inequality follows by exposing the independent blocks, using the conditional range bound 1 for each martingale increment and the exponential Hoeffding bound; it does not require edgewise independence of all compatibility indicators.

For nonempty Q, choose one pattern and partition floor(N/d) fixed outside d-subsets, giving each the same slot order. Each realizes that pattern in G(n,τ) with probability τ^e≥r^b. Hence

    μ_Q ≥ floor(N/d) r^b ≥ c_d n^(99/100).       (5)

The equality/no-edge pattern has probability one and also satisfies this bound. No independence is required for this expectation lower bound.

The number of choices of Y is at most exp(O(n^(2/3) log n)). For fixed Y the number P_Y of labelled patterns is at most

    2^binom(d,2) (sum_{j=0}^s binom(|Y|,j))^d,

whose logarithm is O_d((log n)²), including s>|Y|. The number of Q of size at most M has logarithm O_d(n^(1/100)(log n)²). Counting all families rather than only permutation-closed ones overcounts harmlessly. Thus the total number of tests (Y,Q) is at most exp(K_d[n^(2/3)log n+n^(1/100)(log n)²]).

Use (3)–(5) with t=μ_Q/8 and take a union bound. There is a deterministic class D with probability 1−o(1), uniformly in r,s, on which simultaneously

    W_Q(G;Y) ≤ (9/8) μ_Q                         (6)

for every nonempty admissible Q and every Y. The error is bounded by

    exp(K_d[n^(2/3)log n+n^(1/100)(log n)²]−c_d n^(98/100)).   (7)

Constants may change between occurrences. This tends to zero. Combining (2) and (6), for the Q selected from R,

    ν_R(G;Y) ≤ (9/4) μ_Q.                        (8)

## 5. Packing amplification using exchangeability

Take L=64d independent graphs H_i∼G(n,τ). Their union has law G(n,p). Fix (Y,Q). In H_i choose a maximum Q-packing uniformly among ALL maximum packings, using independent auxiliary randomness. Compatibility is invariant under permutations of [n]−Y. Conditional on its cardinality, the chosen packing is therefore uniform among ALL d-uniform matchings of that cardinality: the permutation group acts transitively on those matchings and the selection rule is invariant. This is a distributional statement, not the false claim that every matching is compatible with a fixed H_i.

By (4), with probability at least 1−exp(−c μ_Q²/N), every H_i has packing number at least μ_Q/2. Put

    a=floor(N/(16d²)),      q=floor(min{μ_Q/2,a}).

Trim each chosen packing uniformly to q edges. Conditional on the size-success event, these trimmed packings are independent uniform q-edge d-matchings. The event factors over the L samples, so the conditioning preserves their independence.

Greedily retain from each trimmed matching the edges disjoint from all edges retained earlier, stopping as soon as a edges have been retained. Before stopping the used vertex set B has size at most d(a−1)<N/(16d). Conditional on the past, any edge of the next uniform matching hits B with probability at most d|B|/N≤1/16. The expected number of its edges avoiding B is at least 15q/16.

For the needed tail estimate, generate a uniform q-edge d-matching by taking a uniform random permutation of N vertices and grouping its first dq positions into blocks of size d. The number of blocks avoiding B changes by at most two under any transposition. In the permutation-exposure martingale, different possible next entries can be coupled by one transposition; each conditional range is therefore at most two. The elementary martingale exponential bound yields

    P(fewer than q/2 blocks avoid B | past) ≤ exp(−c q²/N).   (9)

Using the weaker bounded-increment version gives the same bound with a smaller absolute c. This is uniform over the random B; no union bound over B is needed.

For sufficiently large n (depending on d), (5) ensures μ_Q≥6 and a≥2. If μ_Q/2≤a, then q≥μ_Q/3. If μ_Q/2>a, then q=a. In both cases q≥c_d n^(99/100). After L successful rounds either a edges were retained, or at least Lq/2 were retained. In the first case this is already the cap; in the second case μ_Q/2≤a and

    Lq/2 ≥ (32/3)d μ_Q > 8d μ_Q.

When q=a the cap is reached within two successful rounds. We conclude

    ν_Q(union_i H_i;Y) ≥ min{8d μ_Q,a}           (10)

outside an error exp(−c_d n^(98/100)). All retained blocks are compatible in the union because only edge-presence constraints are used.

Take the union bound over (Y,Q), as in §4. Define E to consist of hosts satisfying (10) for every test. Although its proof used auxiliary layers and tie-breaking randomness, E is a deterministic graph property. If the union host fails E, every choice of the auxiliary witnesses fails at least one test; hence the failure probability of E is at most the joint failure bound. Its law is exactly G(n,p), so E has probability 1−o(1), with the uniform error (7).

## 6. Proof of (T)

For nonempty R, choose its compressed Q. Because Q⊆R up to slot permutations, ν_R(H;Y)≥ν_Q(H;Y). Apply (8) and (10):

    ν_R(H;Y) ≥ min{8d μ_Q,a_Y}
               ≥ min{2d ν_R(G;Y),a_Y},

since 2d·(9/4)μ_Q<8d μ_Q. Empty R gives zero on both sides. This completes the author-level proof of (T).

## 7. Anchored bounded-component extension

As an application, for every G∈D and H∈E, suppose J⊆G has vertex set Y∪W, has no edges within Y, satisfies |Y|≤n^(2/3), |W|≤n/(1000d³), each w∈W has at most s neighbors in Y, and each component of J[W] has at most d vertices. Then J embeds into H fixing every vertex of Y.

Pad each component with fresh isolated nonroot placeholders to order d. At most d|W|≤n/(1000d²) outside vertices are needed, so they can be chosen distinctly in the source. Associate to component i its rooted pattern and let L_i(H) be its d-uniform compatibility hypergraph. For any nonempty I, the padded source components give a matching of size |I| for the family R_I of their types. By (T), and a_Y≥2d|W| for large n,

    ν(union_{i∈I} L_i(H)) ≥ 2d|I| > d(|I|−1).

The Aharoni–Haxell sufficient condition for disjoint representatives of d-uniform hypergraphs now supplies one disjoint compatible block for each component. Its exact contract is stated as Theorem 2.6 in Ferber–Luh–Nguyen, arXiv:1606.05923v3; their entire relevant argument, §2.4, was read. Choose a realizing ordering for each block and discard the placeholders. This gives the claimed embedding. If root-root edges were embedded in an earlier host, this result extends that embedding using H only for the remaining edges; it does not require H to reproduce predetermined root-root edges.

This corollary is not claimed as a separate finding. The main (T) proof is independent of the Aharoni–Haxell input.

## 8. Counterexample attacks and limits

1. **No fixed per-vertex candidate sets.** The exchangeability argument averages over the random host before choosing a uniform optimum. Arbitrary lists on nonroot images destroy it. Forcing every image into the same tiny list also immediately prevents linear amplification. Such lists are outside (T).
2. **Not induced embeddings.** Requiring absent edges is not preserved under union of layers. No induced version follows.
3. **No global spanning conclusion.** A family allowing every d-subset already has ν=floor(N/d); multiplicative improvement without a cap is impossible. The small-support assumption in §7 avoids that obstruction.
4. **No arbitrary common-interface gluing.** Graphs J[W] with growing connected components are not covered. In particular, neither spanning perfect matchings nor arbitrary spanning graph thresholds become constant-factor expectation-threshold statements.
5. **No independence shortcut.** Candidate d-blocks overlap, and their pattern indicators are dependent. All concentration arguments expose vertex incident-edge blocks; only the selected d-blocks are disjoint. Global smoothing is used only via conditional expectation.
6. **No false pointwise symmetry.** A maximum matching of a fixed compatibility graph is not a uniform matching. Uniformity is only after averaging the exchangeable host and random tie-breaker; conditioning on cardinality is safe. Conditioning on a particular realized host would be unsafe.
7. **Root degree and overlap.** The theorem intentionally permits repeated and arbitrarily overlapping A_i across different patterns. A single rare neighborhood can carry many demands only if the source packing actually realizes them. This is why replacing source rank by the number of types or by a first-moment edge count would be false.
8. **Small n, zero patterns, and isolated fillers.** n≥N_d is explicit. Empty R is handled separately; a no-edge pattern is legal. All embeddings are noninduced and fillers have no required edges, so padding imposes no artificial condition.

## 9. Contribution judgment and gate request

(T) is the one nomination. It replaces scalar one-vertex supply by uniform packing rank for arbitrary rooted pattern families, and permits bounded connected components at a shared fixed interface without disjointness assumptions on their root neighborhoods. The full proof above pays the simultaneous-test, smoothing, matching-rank, and exchangeability steps. It is not an algorithmic black-box application, a hereditary corollary, a product, or the earlier rooted matching-entropy inequality.

The nomination is deliberately conditional on INDEPENDENT contribution review: bounded-block embedding via hypergraph matching and sprinkling is classical. Ferber–Luh–Nguyen §2.4 already develops that architecture. Their listed-root sets are disjoint across blocks, while (T) permits arbitrary overlap and selects/compresses an arbitrary union of types against a typical source packing. Whether the uniform rank comparison is a substantial new theorem rather than a routine extension of the pinned compression method is the central contribution-gate question. Worldwide novelty has not been established. There is no acceptance recommendation until both independent gates pass.
