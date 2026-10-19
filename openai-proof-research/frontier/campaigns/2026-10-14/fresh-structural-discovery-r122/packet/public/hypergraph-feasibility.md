# Hypergraph decomposition: prefreeze feasibility and a closing diagnostic

No theorem target was frozen. This is a record of calculations used to decide whether to select a target, not a candidate proof submitted for a gate. The contemplated positive statement was: for every fixed uniformity a>=3, constants k_a,L_a work for every n and every simple a-uniform H on at most n vertices, partitioning E(H) into k_a fixed pieces J with p_c(J;n)<=L_a q(H;n). Here q is the **integral cover** threshold, with cost at most1/2, and containment is ordinary unlabelled containment in the independent binomial a-graph. This full exploratory statement was never replaced by a large-degeneracy, bounded-component or rooted-only statement.

## Actual paid operations

Pinned source175, `Graph-Decompositions.../build/main.tex`, has the same-density finite-ground-set discrete-convexity theorem `thm:discrete`, its deterministic typical cover `cor:typical-cover`, and full graph decomposition `thm:main`. Its `lem:compression` works on an arbitrary finite coordinate ground set. Its `prop:transfer` compresses **all** neighborhood families, bounds smoothed source sums, amplifies the target mean with16 layers, and checks every Hall condition at once. Repeated neighborhoods retain their vertex multiplicities. Its `prop:degree-embedding` has fresh disjoint bins, reverse independent layers, a disjoint-requirement subfamily, and an exponent absorbing both layer count and maximum degree. Its low-degeneracy endgame splits forests into two star forests and uses `prop:stars`. These are stipulated operations, not merely theorem headlines.

[Ascoli–He–Park–Talagrand2608.11183v1](https://arxiv.org/pdf/2608.11183v1), Theorem1.8/Section2, already has the compatible group-action reduction: average the proportion of relabelings belonging to a decreasing family, use its large mean and containment probability to obtain a good relabeling, and use a union bound for one common permutation. Its final Section8 explicitly extends this reduction to fixed-uniformity hypergraphs. The direction is a bound on the k-threshold from decomposable pieces; it is not a theorem giving bounded hypergraph decompositions.

The actual I248/I267 history is stronger than one-vertex Hall. I267 permits arbitrary overlap and repetition of roots for fixed d-slot blocks, uses the maximum weighted packing and its conditional expectation under global addition, (d,0)-self-bounding concentration, and independent equivariant maximum packings conditioned **only on their sizes**. It reaches r^(ds+binom(d,2))>=n^(-1/3)log²n. It explicitly does not handle growing d, prescribed candidate lists or a spanning conclusion. [Ferber–Luh–Nguyen1606.05923v3](https://arxiv.org/pdf/1606.05923v3), Section2.4 Lemmas2.5–2.7, already uses hypergraph matching and Janson estimates for bounded blocks, with disjoint external neighborhoods across blocks and fixed maximum degree. These are real compatible reductions, not missing because their headlines differ.

## Initial dense-core calculation

Let d be the hypergraph degeneracy. Every induced subhypergraph satisfies e(H[S])<=d|S|. A subhypergraph of minimum degree d has e>=dv/a; its labelled copies show q(H;n)>=(1/2)n^(-a/d). Thus when q is bounded above by a sufficiently small fixed constant, d=O_a(log n).

Start with Y0={v:deg_H(v)>sqrt(n)}, so |Y0|<=a d sqrt(n). Fix C>1. While some nonempty U outside Y satisfies

    e(H[Y union U])-e(H[Y]) > C d |U|,

adjoin the whole U. This terminates because the vertex set is finite. Summing the increments over the disjoint added batches gives C d(|Y|-|Y0|)<e(H[Y])-e(H[Y0])<=d|Y| whenever an addition occurred. Hence |Y|<=C|Y0|/(C-1), also if none occurred. At termination the labelled residual multihypergraph, with one edge e\Y for each original edge not wholly in Y, obeys

    #{e not contained in Y : e\Y subset U} <= C d |U|

for every outside U. Multiplicities are essential. It has an elimination order with at most a C d completed edge constraints at each vertex. Original outside degrees remain at most sqrt(n).

This calculation was made **before** the stronger I248/I267 body comparison. It is elementary density closure, not a new abstract closure theorem or a full embedding.

## Correction to the initially suspected interface gap

Initially I treated all crossing hyperedges as one embedding problem and identified possible exhaustion of rare root profiles by earlier placements. That is not an established unpaid operation for the proposed decomposition: the pieces need not have compatible embeddings.

Separate edges with exactly one outside vertex. Their requirements are subsets of binom(Y,a-1); source compression/Hall applies to these Bernoulli coordinates with the corresponding fixed-a test entropy. For edges with at least two outside vertices, each completed requirement contains an earlier outside vertex. Repetition of an identical (a-1)-tuple is therefore bounded by that vertex's original degree, at most sqrt(n). Layering the residual multihypergraph and using fresh bins suggests the source's same disjoint-requirement estimate. For inside-Y pieces, an identical (a-1)-tuple has at most |Y| extensions in a simple hypergraph. Thus the mixed-edge complaint does not justify novelty; the large-d regime has a much stronger compatible source reduction than the initial diagnosis admitted.

No complete parameter-uniform large-d theorem is asserted here. In particular it is not offered as a narrowed replacement. The decisive remaining feasibility check is the bounded-d regime, where r^s need not dominate a small negative power of n and the graph-specific forest/star endgame is unavailable.

## Explicit low-degeneracy diagnostic

The following author calculation closes the contemplated **full positive extension**, rather than just refuting one greedy algorithm. It is retained as prefreeze screening evidence, not nominated as a new result; there has been no independent correctness or contribution review. The construction is the classical hedgehog of Conlon–Fox–Rödl, not an original hypergraph construction.

For an integer t>=3 let n=t² and take a core of t vertices. For every core pair {i,j}, add its own new vertex w_ij and the triple {i,j,w_ij}. Let H_t be this3-uniform hypergraph. It has m=binom(t,2) edges and t+m<=n vertices. It is linear and1-degenerate: every nonempty edge subhypergraph retains a degree-one private vertex.

First, q(H_t;n)<=C0/n for C0=3e³ and all sufficiently large n. Choose a uniformly random injection of all vertices of H_t into[n] and let F be its edge set. For any fixed nonempty triple set S, write s=|S| and v=|V(S)|. If S does not embed in H_t its containment probability is zero. Otherwise an embedding chooses, for each edge, which of its three vertices is its private leaf. There are at most3^s choices. In any valid choice these s designated leaves are distinct and none is a core vertex. Thus k=v-s is the number of core vertices, with0<=k<=2s. There are at most t^k images for these core vertices, after which each leaf is forced by its pair. Consequently

    Pr(S subset F) <= 3^s t^k/(n)_(s+k).

For0<=v<=n, (n)_v>= (n/e)^v. One proof compares the decreasing function log(1-x/n) with its integral on[0,v]; the integral is at least -v. Since t=sqrt(n),

    Pr(S subset F) <= 3^s e^(s+k) n^(-s-k/2) <= (3e³/n)^s.

If a family covers every copy of H_t, it covers every F in this distribution. The union bound therefore forces its cost at C0/n to be at least1. Such a family cannot have cost at most1/2 there or at a larger parameter. This proves the asserted upper bound on the **integral** q; it is not a substitution of the simpler subgraph expectation threshold.

Second, fix any positive integer k0. Every partition of E(H_t) into k0 pieces has one piece J containing s>=m/k0 edges. Take

    p_n = log(n)/(8n).

Any embedding of J can be extended to assign all t original core labels distinct images. There are at most n^t possible core assignments. Each retained core pair must have a completing vertex outside the entire assigned core. For a fixed core assignment, distinct pairs use disjoint sets of triple coordinates: every tested triple has exactly two core vertices. These pair events are independent, even though pairs can share a core vertex. Ignoring the requirement that the completing leaves be distinct only enlarges the containment event. Hence

    Pr(J subset G^(3)(n,p_n))
      <= n^t [1-(1-p_n)^(n-t)]^s
      <= exp(t log n - s (1-p_n)^(n-t)).

For sufficiently large n, p_n<=1/2 and log(1-p_n)>=-2p_n. Thus (1-p_n)^(n-t)>=n^(-1/4). Also m>=n/3 for t>=3. The exponent is at most

    sqrt(n) log n - n^(3/4)/(3k0),

which tends to minus infinity. This bound is uniform over all pieces with at least m/k0 edges; no union bound over partitions is needed. For every fixed k0 and every fixed finite L, eventually the selected piece has p_c(J;n)>p_n while L q(H_t;n)<=LC0/n<p_n. Therefore the contemplated universal fixed-k0/fixed-L positive extension cannot hold.

This does not refute source175, which concerns graphs. It does not refute fixed-uniformity k-threshold bounds: the reduction direction above is only sufficient. It does not establish an optimal hypergraph decomposition tradeoff or an all-hypergraph classification. No restricted positive repair is nominated.

## Primary comparison and reading boundary

[Conlon–Fox–Rödl1511.00563v1](https://arxiv.org/pdf/1511.00563v1), introduction and complete Section2/Theorem1 proof, already constructs this exact hedgehog and converts missing body-pair colors into hypergraph obstructions. Its lower bound uses a first-moment coloring and body projection; its upper bound uses plentiful completions and greedy distinct spines. The present feasibility calculation uses the same classical body/private-leaf structure, a uniform-injection counting estimate, and a first-moment bound. No unpaid source-dependent mechanism is claimed. The primary's Section3 was only partly read and no worldwide novelty conclusion follows from the searches.
