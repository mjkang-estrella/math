# Mathematical investigation; no nominated discovery

## 381600: exact reduction and remaining gap

Primary: Celoria, arXiv:2105.03987, fetched PDF hash in sources/receipts.json; Section 5, Equation (8), Definitions 5.2 and 5.5, Conjectures 5.1 and 5.4. The graphs are finite, simple, connected, unlabelled up to isomorphism, with a common number n of vertices. The intended claim is that equality of every Θ(G,j), 0≤j≤n, forces isomorphism. A disconnected witness or relabelling is inadmissible.

For a black vertex set S, let k=|S|, e=e(G[S]), c=the number of connected components of G[S] (zero for S empty), q=the number of edges between S and its complement W, z=the number of vertices of W with no neighbour in S, and m=|E(G)|. The only potentially nonzero horizontal homology ranks, in order (homological degree, filtration degree), are

- (0,0): c;
- (1,0): e-k+c;
- (0,1): z;
- (1,1): q-(n-k)+z;
- (1,2): m-e-q.

Proof over any field: the filtration-zero boundary is precisely the oriented incidence matrix of G[S], whose rank is k-c. This follows by choosing a spanning tree in each connected component: its edge columns are independent, by removing leaves, and every remaining column is a signed sum of tree columns. In filtration one, each mixed edge has as boundary its white endpoint (up to sign), and different white endpoints have disjoint supports. Therefore this boundary has rank n-k-z. In filtration two the white-white edges have zero horizontal boundary, and there are no vertices or higher simplices in this filtration. Subtracting these boundary ranks from chain dimensions gives the five assertions. No higher homology groups occur because the graph is a one-dimensional simplicial complex.

The evaluator retains, for every k and every bidegree, the histogram of all positive ranks, with multiplicity, forgetting the label S. It also computes the stronger joint histogram of all five ranks. A collision of the joint histogram would imply a collision of either the marginal-histogram interpretation or summed-rank interpretation of Θ. All search calculations use integers, not floating point. Direct F_2 boundary elimination independently validated 3,600 colouring instances, including empty/full subsets in the random sample; prism versus K3,3 is a negative control for the isomorphism checker and metric.

Two bounded samples (see metric-diagnostics*.json) evaluated 1,564 connected regular graphs on 10 or 12 vertices and 486 on 14 or 16 vertices. There were respectively 440 and 446 distinct marginal signatures, and no nonisomorphic equal-signature pair. Samples are not canonical graph enumerations; repeated isomorphic graphs occur. Limits: 800 MiB address space, 110 CPU seconds per process; 75 and 40 second wall budgets, with at most 1800/1200 attempts. The first run actually finished after 1800 attempts in about 9 seconds. These calculations do not prove the conjecture or establish exhaustion.

A second mechanism, gluing graphs across two vertices and reversing the terminals on one side (Whitney flip), was tested explicitly. The connected nonisomorphic pair in whitney-obstruction.json already has different (0,1) rank histograms for k=2: rank 1 occurs twice versus three times. Thus preservation of cycle-matroid data alone cannot certify preservation of this invariant. This rejects this particular construction, not all Whitney-flip constructions.

### Essential source-fidelity obstruction

Definition 5.2 says to group tuples with the same (j,i,k); the worked Example 5.3 prints a grouped (2,1,2,54), visibly an aggregate, and prints other bidegrees inconsistent with the incidence calculation (including a nonzero (1,0) rank for an induced two-vertex graph). The paper simultaneously claims detection of degree sequences and all trees through 16 vertices. These assertions cannot hold for an interpretation that keeps only summed ranks. PDF page 19 was visually inspected; its PNG is preserved. This is not an OCR inference alone.

Indeed for any tree T and fixed k, summing the five ranks over all |S|=k gives, with binomial coefficients outside their natural ranges defined to be zero:

C_k = k*binom(n,k) - (n-1)*binom(n-2,k-2),
B_k = 0,
Z_k = sum_v binom(n-1-deg(v),k),
R_k = 2*(n-1)*binom(n-2,k-1) - (n-k)*binom(n,k) + Z_k,
E_k = (n-1)*binom(n-2,k).

Proof: every induced subgraph of a tree is a forest, so c=k-e and e-k+c=0. Each edge is black-black in binom(n-2,k-2) subsets, mixed in 2*binom(n-2,k-1), and white-white in binom(n-2,k). For a fixed v, it is white and has no black neighbour in binom(n-1-deg(v),k) subsets. Sum the rank formulas. Thus summed Θ cannot distinguish trees with the same degree multiset. The six-vertex trees with arm lengths (3,1,1) and (2,2,1) about their unique degree-three vertex give an immediate example. Their degree multisets agree and they are nonisomorphic because distance from the unique degree-three vertex to its farthest leaf is respectively 3 and 2. This is recorded solely as an interpretation/consistency obstruction. It is not nominated as a new significant refutation; it conflicts with the author's stated computational intent and is exactly the kind of wording/definition issue that receives zero credit under this assignment.

Remaining actual mathematical gap: under the stronger histogram interpretation consistent with the paper's intended discriminatory power, produce a nonisomorphic connected pair with equality for every k, or reconstruct a graph from these distributions. Neither direction is proved. A viable next step is a rooted-gadget transfer calculation preserving simultaneously induced component ranks and undominated-white counts; equality of Tutte/Ising data alone does not supply this bridge. No universal reconstruction lemma or valid collision was found.

Lean feasibility: an explicit modest-order collision would permit a kernel-checked finite graph certificate, with separately proved bridges from boundary ranks to these combinatorial formulas, exact histogram equality, connectedness, and nonisomorphism. No source endpoint or Lean code exists here. The mathematical reduction is elementary source unpacking and merits no discovery credit itself. Source interpretation must be resolved before formal implementation.

## 381795: routine product route; zero credit

Primary: Brenti–Sentinelli, Section 4 explicit bijection φ and Conjecture 6.4. Earlier repository work on the unsigned analogue is in expanded-corpus-r120/results.json (381794); signed Möbius work is in expanded-corpus-r99 (381793). This makes this a family-adjacent candidate, not a clean new investment.

The signed even-case vertex formula gives a short product argument. On each consecutive coordinate pair (x_(2i-1),x_(2i)), apply the invertible linear map (s_i,d_i)=(x_(2i-1)+x_(2i),x_(2i-1)-x_(2i)). The vertex set becomes all signed permutations of (3,7,...,4m-1) in the s coordinates times all independent sign vectors in the d coordinates. The signs are independent because the subset T in φ toggles each pair's order independently of σ. Thus the hull is P_B × [-1,1]^m, where P_B is the signed permutahedron for these distinct strictly positive magnitudes.

For completeness, P_B is simple: a linear functional with nonzero pairwise distinct absolute coefficients is uniquely maximized by matching coefficient signs and sorting magnitudes. Its normal cones at vertices are the signed-order chambers 0≤ε_1 a_(π1)≤...≤ε_m a_(πm). Each chamber is a full-dimensional simplicial cone, obtained by invertible signed permutation from 0≤a_1≤...≤a_m. Thus each vertex has exactly m incident facets. The cube is simple and a product of simple polytopes is simple, since the numbers of incident facets and dimensions add. This proves the displayed source simplicity via classical polytope facts, with no substantial new mechanism. It is excluded from discovery credit as a routine signed analogue of the already documented unsigned product argument. No formal implementation or independent review requested.

## 382260: primary reviewed, not solved

The fetched current source still states its low-betweenness BUG classification as Conjecture 2; the 2026 journal page also states it. The earlier conjecture concerning all rational betweenness values is already refuted by the authors and is a different question. Source Section 3 rules out all complements composed solely of uniform components and star components of size at most nine; any counterexample must contain large stars and a nonuniform non-tree component. No new construction bypassing those source obstructions was found. Searching a small graph atlas would not be a promising next step. No proof or counterexample is claimed.
