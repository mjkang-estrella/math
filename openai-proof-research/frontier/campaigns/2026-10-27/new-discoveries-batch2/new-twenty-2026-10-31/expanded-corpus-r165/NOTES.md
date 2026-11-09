# expanded-corpus-r165: mathematical notes

None of these arguments is a creditable result. Each one is recorded so that a reviewer can check the dispositions in results.json.

## 1. 334808: G_SR is never K_{r,s} with r, s ≥ 2 (already known: Lenin, DAM 265 (2019) 204–205)

Definitions follow the source (arXiv:1612.02843, Section 1.3). A vertex u is maximally distant from v when d(w, v) ≤ d(u, v) for every neighbour w of u. Two vertices are MMD when each is maximally distant from the other. The boundary ∂(G) is the set of vertices that are MMD with some vertex. G_SR has vertex set ∂(G), with an edge between each MMD pair. σ(G) is the set of simplicial vertices.

**Lemma A (maximal geodesic extension).** In a finite connected graph, every geodesic P is a subpath of a geodesic x…y whose endpoints x and y are MMD.

*Proof.* Among the geodesics that contain P as a subpath, choose one of maximum length, from x to y. Suppose y had a neighbour y′ with d(x, y′) = d(x, y) + 1. Then appending y′ would give a longer geodesic containing P, a contradiction. So y is maximally distant from x, and by symmetry x is maximally distant from y. ∎

**Lemma B.** If v ∈ ∂(G) \ σ(G), then G_SR has an edge xy such that v is adjacent in G_SR to neither x nor y.

*Proof.* Since v is not simplicial, it has neighbours v1 and v2 with d(v1, v2) = 2, so v1 v v2 is a geodesic. Lemma A extends it to a geodesic x…v1 v v2…y with x and y MMD. On that geodesic v1 is farther from y than v is, so v is not maximally distant from y. Likewise v2 shows that v is not maximally distant from x. ∎

**Theorem.** If G_SR ≅ K_{r,s} with parts U1 and U2, then every boundary vertex is simplicial. Hence G_SR is complete (the source's Theorem 10), which forces r = s = 1.

*Proof.* Suppose v ∈ U1 were not simplicial. Lemma B gives an edge xy of G_SR. One of x and y lies in U2, so v is adjacent to it in G_SR, contradicting Lemma B. The last step uses the fact that simplicial vertices are pairwise MMD. ∎

Lemma B is the source's own Lemma 9 with one added observation: the extension endpoints can be taken MMD. That makes this a short source-machinery bridge, and the statement was already published in 2019.

Exhaustive check (diagnostic): no realization among all connected graphs of orders 4–9, or among the first 3,000,000 connected graphs of order 10.

## 2. 331819: Conjecture 4.4 is equivalent to "there are no hypotraceable graphs"

Here ψ_k(G) is the minimum size of a vertex set that meets every path on k vertices (source abstract). Let n ≥ 3.

- A path on n − 1 vertices misses exactly one vertex. So any two vertices together meet every such path, and ψ_{n−1}(G) ≤ 2.
- A single vertex v meets every (n − 1)-vertex path exactly when no such path avoids v, that is, when G − v is not traceable.

Hence ψ_{n−1}(G) = 2 if and only if every G − v is traceable. Also, ψ_n(G) = 1 if and only if G is traceable.

So the conjecture says that no non-traceable graph has all of its vertex-deleted subgraphs traceable, which is exactly the claim that hypotraceable graphs do not exist. That is false by the classical hypotraceable graphs: Horton's 40-vertex example and Thomassen 1974 (34 vertices). Such graphs are connected. Under MathDB's paraphrase (ψ_k as a path count), a spider with legs 1, 1, 2 is a 5-vertex counterexample. Both refutations earn zero credit.

## 3. 331535: a routine corollary of the public CDC theorem

Assume a cycle double cover (CDC) exists for every bridgeless loopless multigraph (openai/cdc-lean, `cycleDoubleCover_of_bridgeless`). Let G be k-regular and (k − 1)-edge-connected.

- k ≤ 2: trivial. For k = 2, G is a cycle and that cycle is a 1-cover. For k = 1, the empty list is a 0-cover.
- k ≥ 3 odd: G is bridgeless, so (k − 1)/2 copies of a CDC form a cycle (k − 1)-cover.
- k ≥ 4 even: every degree is even, so E(G) decomposes into circuits (Veblen), giving a 1-cover. Add (k − 2)/2 copies of a CDC.

## 4. 329577: Christoffel–Darboux form

Set p_k(x) = Σ_j C(k, j) C(k + j, j) x^j = P_k(2x + 1), and let L_r be the linear functional with L_r(x^j) = 1/(2j − 2r − 1). Then R_{k,r} = L_r(p_k).

The Christoffel–Darboux formula gives Σ_{k<n} (2k + 1) P_k(u) P_k(v) = n (P_n(u) P_{n−1}(v) − P_{n−1}(u) P_n(v)) / (u − v). With u = 2x + 1 and v = 2y + 1, this yields

S_n = Σ_{k<n} (2k + 1) R_{k,r}² = n · (L_r ⊗ L_r)(Q_n) / 2,

where Q_n = (p_n(x) p_{n−1}(y) − p_{n−1}(x) p_n(y)) / (x − y) has integer coefficients.

So the conjecture is equivalent to a bound, uniform in n, on the denominator of (L_r ⊗ L_r)(Q_n)/2. Exact computation for r ≤ 7 and n ≤ 120 gives the least constants 1, 9, 225, 3675, 99225, 2401245, 135270135, 289864575. Each divides the authors' suggested ((2r + 1)!!)². No uniform proof was found.
