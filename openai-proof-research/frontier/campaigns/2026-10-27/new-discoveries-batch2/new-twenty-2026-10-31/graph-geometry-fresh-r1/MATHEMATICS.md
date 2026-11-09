# Mathematical record — zero resolution credit

## 319783: restored endpoint

Haws–Hodge–Yoshida, arXiv:1004.2073, §§2.1, 2.3, 3, 6: n≥3; trees are unrooted, with leaves bijectively labeled by X={1,…,n}, all internal vertices of degree three, and no edge lengths as part of the combinatorial object. Coordinates are unordered leaf pairs in lexicographic order. If d_T(i,j) counts edges on the unique path, w_T(i,j)=2^(1−d_T(i,j)). P_n is the convex hull of the vectors of **all** such trees. Theorem 1 proves SPR adjacency implies adjacency in P_n. Conjecture 1 asks whether one TBR move implies adjacency. It is not enough to find an edge in the convex hull of a chosen neighborhood.

A TBR move deletes an edge, suppresses the degree-two endpoints that result, chooses an edge in each component, subdivides these two edges with new vertices, and joins the new vertices. The singleton-component convention gives SPR cases. The experiments only cut internal edges, whose two components have at least two leaves; their suppressed components therefore have edges available for reconnection. Identical outputs are discarded when selecting pairs. The source definition of adjacency requires distinct tree vectors and an actual edge of P_n.

## Exact certificate criterion (proved here, helper only)

Let u,v be distinct vectors in a polytope P. Suppose q=αu+(1−α)v, 0<α<1, and also q=Σ_j β_j z_j with β_j≥0, Σβ_j=1, z_j∈P. If some β_j>0 has z_j outside the line through u,v, then [u,v] is not a face of P, hence is not an edge.

Proof: If [u,v] were a face, its defining face property applied to the convex combination for q forces every positive-weight z_j into [u,v]. For completeness, isolate z_j: if β_j=1 then q=z_j, which contradicts its being off the line; otherwise q=β_j z_j+(1−β_j)y with y∈P, and the face property implies z_j∈[u,v]. Contradiction. No assumed extremality premise is used. Thus a nonedge certificate can be checked without enumerating all vertices, provided each z_j is established to be a correctly weighted valid binary tree. A literal Lean refutation would still require all those graph, path, TBR, convex-hull, and face bridges.

The search uses integer vectors W_T=2^(n−2)w_T, whose coordinate is 2^(n−1−d_T(i,j)). Its feasibility system is

    Σ β_j W_j + α(W_v−W_u) = W_v,
    Σ β_j = 1, β_j≥0, 0≤α≤1.

For an actual certificate require α strictly between zero and one, rational coefficients, exact equality in every coordinate, and a positive coefficient off the endpoint line. A successful floating LP alone is insufficient. The programs include rational reconstruction and coordinate checking for discovery, but **no successful LP occurred**, so there is no candidate certificate.

## Surviving algebra: four reconnections do not automatically give a parallelogram

Fix two unrooted binary component trees on disjoint leaf sets A,B. Choose attachment edges a_0,a_1 in the first and b_0,b_1 in the second. Let T_ij be their reconnection. Inserting the attachment vertex gives a rooted component; let p_i(x)=2^(−distance(x,root_a_i)) and q_j(y)=2^(−distance(y,root_b_j)). For x∈A,y∈B the path consists of the two component paths and the connecting edge, so

    w_Tij(x,y)=p_i(x)q_j(y).

For a pair of leaves both in A, the path is wholly within A and is independent of j; similarly weights inside B are independent of i. Consequently D=w_T00+w_T11−w_T01−w_T10 vanishes on pairs within a component and satisfies

    D(x,y)=(p_0(x)−p_1(x))(q_0(y)−q_1(y))

on cross pairs. If both profile differences are nonzero, this tensor has a nonzero coordinate: choose an x and a y with nonzero factors. Hence the naive equal-weight four-tree parallelogram is not a nonedge certificate in this case. This identity is only a helper, not a resolution or a new-literature claim.

The decisive next calculation is to solve for an exposing objective on the face of trees sharing the TBR split, adding corrections to the rank-one cross objective so it controls every other attachment position and component topology. If c exposes precisely the target pair on that face, one must also prove a finite face-extension step to the full polytope. Forcey–Keefe–Sands Theorem 4.3 supplies a known face for refinements of a nonbinary tree; it does not assert that every pair of its vertices is an edge. Restricting to a shared split by itself leaves many vertices and does not finish the target.

## 320847: restored endpoint and set cover

Bailey–Stevens, published Australasian Journal of Combinatorics 50 (2011), 219–231, Definition 2 and §4: for a connected graph G=(V,E), a t-UBB is a collection U of spanning trees such that for every F⊆E with |F|=t, some T∈U has E(T)∩F=∅. In this paper t=λ(G)−1. The published conjecture explicitly says **at most |E(G)|**. The cached MathDB statement and an older author preprint say exact cardinality. We investigate the substantive upper-bound endpoint and do not claim any wording correction as credit. The published graph model is finite undirected, and its displayed constructions are simple; it does not explicitly settle every convention about loops/multiple edges or λ=1/t=0. Our computations use finite connected simple graphs with λ≥3, so they do not depend on those boundary conventions.

Exact failure cardinality t also covers all smaller failure sets whenever t≤|E|: extend any smaller set to a t-subset and use its disjoint tree. This is a routine quantifier bridge, uncredited. Any t-set can be deleted without disconnecting G when t<λ, which proves existence of some avoiding tree, but choosing a different tree for every failure set gives only a binomial-size family, not the conjectured linear bound.

Let S be the set of all spanning trees and F the family of all (λ−1)-edge sets. Define A_(F,T)=1 if F∩E(T)=∅. The exact optimization is min Σ_T x_T subject to A x≥1, x_T∈{0,1}. A rational dual obstruction would consist of y_F≥0 satisfying Σ_(F disjoint T)y_F≤1 for **every** spanning tree, with Σ_F y_F>|E|. For any covering family U, summing its coverage gives Σ_F y_F≤Σ_(T∈U)Σ_(F disjoint T)y_F≤|U|, a contradiction. This is a sufficient obstruction; failing to find such a fractional obstruction would not prove the integral bound. The dual constraints must cover every spanning tree, not merely a sample.

The actual experiment instead enumerates spanning trees on 45 sampled simple graphs (6–8 vertices, at most 18 edges), computes λ by all cuts, and greedily selects trees avoiding the most remaining failure sets. All selected families have at most |E| members and pass a fresh exact all-failure-set validation. This proves only the stored instances. No optimality or set-cover lower bound was computed. The next substantive UBB calculation would be a rational dual search on a graph outside the already proved Hamilton-decomposition, complete-bipartite, wheel, and max-STP families, followed by a complete-tree verification if the dual objective exceeds |E|. No such graph or dual witness is presently identified.

## What was actually run

* Full generated tree pools: n=7 (945 trees), 50 sampled TBR pairs; n=8 (10,395 trees), 100 pairs; n=9 (135,135 trees), 30 pairs. All 180 LP results were HiGHS status 2. These floating infeasibility reports are not exact edge certificates and are not claimed as proofs. Sampling caps mean the early bases can consume the whole cap; these are not uniformly sampled pairs or all TBR orbits.
* Local pools: n=12, 12 pairs (541–765 other columns); n=16, 12 pairs (1,823–2,346 other columns). At n=16 trials 8 and 11 have status 4 (solver error), explicitly inconclusive. The other 22 local LPs report status 2. Local infeasibility gives no full-polytope conclusion.
* n=9 completed in 169.329 seconds. An attempted stop after observing approximately 1.084 GB RSS found the process already finished. The initial interrupt note is retained with a correction. No run was left active. No larger full tree enumeration was attempted. Later code adds a 15-second per-LP time limit; the original completed runs predate that edit.
* The first n=7 invocation failed before any LP due to unsorted initial edge pairs. This was corrected, and the successful run is separate evidence. Fresh structural checks validate all n=7,8 generated graphs, split-key uniqueness, exact Kraft row sums, and one full generated TBR neighborhood for each n. These are Python checks, not a Lean completeness theorem for the enumerator.
* UBB runs and fresh checks are integer/bitset computations; they require no numerical LP decisions.

No full endpoint closed. No Lean endpoint, axiom audit, clean extracted Lean replay, paper claiming a solution, or independent acceptance review exists. Zero accepted/discovery credit for both IDs.
