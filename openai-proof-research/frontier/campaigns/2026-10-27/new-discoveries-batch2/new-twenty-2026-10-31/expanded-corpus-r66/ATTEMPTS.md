# Sustained routes, 2026-11-01

No endpoint or credit is proposed. These are investigations, not formal certificates.

## 371170: average size of subsets inducing exactly one edge

Source: arXiv:2510.23670, Section 2, definitions and Section 4, Conjecture 1. A 1-nearly independent set induces **exactly one edge**; it does not merely have maximum degree one. The conjecture is about all trees of the same order, with R_n obtained by subdividing one edge of S_(n-1). The preceding n>8 theorem does not establish the maximizer.

For an edge uv, put F_e=T-(N(u) union N(v)), using open neighborhoods (their union already contains u and v). Every qualifying set has a unique edge e and is uniquely {u,v} union an independent set of F_e. Thus, with I(F) the independent-set count and J(F) its total size,

A(T) = 2 + (sum_e J(F_e))/(sum_e I(F_e)).

The source already uses this reduction. It is a starting point, not a discovery. For a forest F, A_0(F)<=|V(F)|/2. Hence the deficit from (n+1)/2 is the I(F_e)-weighted average of

(d(u)+d(v)-3)/2 + (|V(F_e)|/2-A_0(F_e)).

Here |N(u) union N(v)|=d(u)+d(v) because a tree has no triangle. The first term is nonnegative for a tree of order at least 3. To prove the conjecture one needs the *quantitative* lower bound

sum_e I(F_e)*[(d(u)+d(v)-3)/2 + (|V(F_e)|/2-A_0(F_e))]
 >= [(n^2-13n/2+21/2)/(2n-5+2^(n-3))] * sum_e I(F_e).

The forest bound alone only gives positivity and cannot establish this exponentially small sharp deficit. Edges of degree pair (1,2) have zero structural term; their residual forests can dominate the weights. Controlling all such weights, together with the residual independent-set deficits, is the unresolved structural step. No leaf transfer preserving the ratio was proved.

Three concrete investigations:

1. Exact rooted dynamic programming: states record whether the root is selected, and whether the induced subset has 0 or 1 edges. Each state stores its count and total cardinality. Combining child states adds the connecting edge iff both roots are selected, and discards states with more than one edge. All nonisomorphic trees for 4<=n<=16 were checked (32,505 trees total). R_n is a maximizer throughout. This is bounded evidence only. An independent literal enumeration of all vertex subsets checks the DP on every tree through n=9.
2. Double stars D_(a,b) (a,b>=1, n=a+b+2). Direct conditioning gives count 1+a*2^b+b*2^a and total excess above twice the count equal to ab*(2^(b-1)+2^(a-1)). Therefore A(D)=2+ab*(2^(b-1)+2^(a-1))/(1+a*2^b+b*2^a). R_n=D_(n-3,1). Every such pair through n=100 was compared exactly; none exceeds R_n. This is a family diagnostic, not an all-parameter inequality proof.
3. Spiders with a legs of length 1 and b>=2 legs of length 2 were checked exactly for n<=60, all a>=0, a+2b=n-1. None exceeds R_n. Multiple (1,2) edges therefore did not supply an immediate counterexample. This does not address arbitrary long limbs or branched cores.

Lean prospects: explicit small counterexample would permit a finite, sound induced-edge checker plus tree and average bridges. A positive full theorem would require new graph surgery/weighted-deficit work, followed by semantic finite-set and graph proofs. No formalization of a surrogate is offered.

## 371040: diameters of perfect-matching orbital graphs

Source arXiv:2510.17135, Conjecture 6.2 and definitions in Sections 1–2. Vertices are perfect matchings of K_(2n). Two matchings have relation mu when their union, retaining parallel common edges, consists of alternating cycles of lengths twice the parts of mu. The identity relation must be omitted to obtain connected nontrivial graphs; taking its empty-edge graph as a counterexample would be an excluded scope correction. The source reports verification through n=10.

The switch graph mu=[2,1^(n-2)] has distance n-c(M union P): a switch changes the number of alternating cycles by at most one and one can split each nontrivial alternating cycle successively. Its diameter is n-1. This is known, and the source cites Jennings.

First route: simulate switches by a bounded number of mu-steps. Even a uniform two-step simulation would give 2(n-1), which is insufficient for the exact conjecture. Second route: greedily choose a mu-neighbor increasing the number of cycles relative to the target. This cannot hold globally: if M and target differ by a single switch but mu is a longer cycle type, an increase forces reaching the target, and they are not mu-adjacent. Thus a simple monotonically splitting potential is false as a proof mechanism. Third route: batch the residual switching defects into one mu-move and a short closing phase. No universal realization lemma was obtained. The unresolved lemma is a factorization of every matching displacement into at most n-1 elements of the relevant double coset of the hyperoctahedral stabilizer, uniformly in nontrivial mu. Do not confuse eigenvalue evidence with a diameter proof.

No new numerical sweep was run here because the primary source already reports the small-order range, and that range cannot settle the uniform factorization lemma. No Lean endpoint.

## 371212 / 371211: rigidity degree thresholds

Source arXiv:2510.25689, Conjectures 1.4–1.5. Generic rigidity concerns generic frameworks in R^d, not just connectivity or an edge count. For 371212 the unresolved range after Theorem 1.7 is 2d+2<n<d(d+2), with d>=4 after the special cases. This is where a counterexample would have to survive the known results.

First mechanism: two cliques glued along s vertices, with two nonempty sides of orders a and b. A nonedge crosses the sides, so its degree sum is (a+s-1)+(b+s-1)=n+s-2. To satisfy eta>=n+d-2 requires s>=d. The usual hinge obstruction uses s<=d-1 and misses the required threshold by at least one. It does not refute the conjecture.

Second mechanism: complete bipartite quadrics. For K_(a,b) with a<=b, eta=2a<=n. Thus eta>=n+d-2 is impossible for d>=3. Adding a universal clique of size r lifts both dimension and the threshold by the same 2r: eta rises by 2r while n+d-2 rises by 2r. The deficit is invariant; coning cannot repair this obstruction.

Third mechanism: Maxwell edge shortage. This is explicitly addressed by the source around (2) and Lemma 7.1; the degree-sum threshold in the required range dominates that elementary obstruction. A candidate would need a flexible graph meeting both the nonedge-sum and edge-count conditions, not merely a sparse hinge or quadric. No such graph or exact rigidity-matrix certificate was found. A generic rigidity semantic Lean bridge would be substantial even for a finite witness. Park, with zero credit.

## 370838: source error, not a discovery candidate

The required prior lead arXiv:2507.14568 was fetched before the other primary papers, including v1 on follow-up. Its current v3 discusses Albertson bounds; it does not by itself establish a Sigma-index subsumption bridge. The actual source arXiv:2510.06845 Conjecture 1 quantifies over **caterpillars**, not all trees, and includes a purported proof immediately afterwards. The proof asserts the desired right inequality without deriving it.

For the path P_4, a caterpillar with n=4,m=3,Delta=2, at k=1 the middle expression equals 49/4>2. This is an elementary parameter-only violation; it does not depend on evaluating the Sigma index at all. It is logged as a defect in the bound and excluded under the campaign's substantive standard. No credit or Lean investment is proposed for this trivial correction. The source's purported proof must not be treated as a valid resolution.
