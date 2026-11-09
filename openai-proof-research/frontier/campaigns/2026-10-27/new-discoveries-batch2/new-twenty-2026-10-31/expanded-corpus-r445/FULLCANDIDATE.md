# MathDB 351988: ordinary full-scope proof proposal, scientific HOLD

No credit. Not independently reviewed, not formalized, not accepted. Investigator is GPT-6.1 Sol high/default, no children. This is a complete ordinary argument proposed for adversarial review, not an independent acceptance finding.

## Literal and source
The entire original object and exact statement token are in originals.json and literals/351988.jsonl. For finite unweighted trees T,T' with the same number n of vertices, assume hom(T,G)>=hom(T',G) for every finite simple graph G. The requested conclusion is alpha(T')>=alpha(T), where alpha=n^(-2) sum_{u,v} H(u,v), with diagonal hitting times zero. The loaded primary source is Ji Zeng, arXiv:2109.09249v4, dated 2 April 2026, pp.1,3,8 (definitions, forest formula Lemma2.1, concluding question). Its proof sections3–4 were read too. PDF SHA256 fb02dc62255831388ee9b0b4190972e93fc386ab7b0df3e20f4627e545c44eb7. Figure4 on p.8 visually inspected; it depicts a different size-transfer order, not the Sidorenko order. The proposed proof does not identify these orders.

## 1. Extend the hypothesis to one bounded kernel, with no black-box graphon theorem
For c>0 set K_c(x,y)=exp(-c(x-y)^2/2), and let gamma be standard normal probability measure on R. Define
Z_F(c)= integral over R^{V(F)} of product_{uv in E(F)} K_c(x_u,x_v) d gamma^{V(F)}(x).
This integral exists, between zero and one, because its integrand is measurable and bounded.

Here is a direct finite-simple-graph bridge. For each N>=n, sample independent X_1,...,X_N of law gamma. Conditional on them, put an edge between each distinct pair i,j independently with probability K_c(X_i,X_j). Put no loops. This is a random finite simple graph. Each injective map f:V(F)->[N] is a homomorphism with probability exactly Z_F(c): distinct source edges use distinct unordered target pairs, hence conditional independence applies, followed by integration over the distinct independent X's. Thus
E hom(F,G_N) = (N)_n Z_F(c) + R_F(N),
where 0<=R_F(N)<=N^n-(N)_n. The remainder includes every noninjective map and needs no independence assertion. By the union bound, [N^n-(N)_n]/N^n <= binom(n,2)/N. The assumed inequality holds for every realization G_N, and hence for expectations. Divide by N^n and let N tend to infinity. As both source orders equal n, this gives Z_T(c)>=Z_T'(c). No actual samples, computation, finite search, or mathematical program were run; this is an ordinary probabilistic proof.

## 2. Evaluate the kernel integral
Let L_F be the real combinatorial Laplacian: diagonal degree, off-diagonal -1 at an edge, zero otherwise. Then x^t L_F x=sum_{uv in E(F)}(x_u-x_v)^2. The joint normal density times the kernel product is
(2 pi)^(-n/2) exp[-x^t (I+c L_F)x/2].
L_F is symmetric positive semidefinite, by the displayed sum of squares. Orthogonally diagonalize it; the orthogonal change of variables has absolute Jacobian one and eigenvalues lambda_i>=0. Tonelli and the one-dimensional substitution z=sqrt(1+c lambda_i)y give
Z_F(c)=product_i (1+c lambda_i)^(-1/2)=det(I+c L_F)^(-1/2).
The one-dimensional identity follows from the normalizing Gaussian integral integral exp(-z^2/2) dz=sqrt(2 pi). That identity itself follows by squaring the integral, using polar coordinates in the plane, and evaluating integral_0^infinity exp(-r^2/2)r dr=1. All determinants here are strictly positive. Consequently
D_T(c):=det(I+c L_T) <= det(I+c L_T')=:D_T'(c), for every c>0.

## 3. Identify the two highest coefficients without assuming a matrix-tree theorem
Orient a tree's n-1 edges arbitrarily and write B for its n by n-1 incidence matrix (one +1, one -1 per column). Then L=BB^t. Sylvester's determinant identity and principal-minor expansion, followed by Cauchy–Binet, give
D_T(c)=sum_{S subset E(T)} c^{|S|} sum_{R subset V(T), |R|=|S|} det(B_{R,S})^2.
For completeness, Sylvester's identity follows by eliminating either off-diagonal block in the block matrix [[I,B],[-cB^t,I]], and principal-minor expansion follows by choosing identity entries on the complementary rows in the Leibniz determinant formula.

The graph (V,S) is a forest. Let its component orders be a_1,...,a_k, so |S|=n-k. A square submatrix B_{R,S} has nonzero determinant exactly when R omits one vertex in every component. To verify: each component's incidence block has rank a_i-1, since the sum of its rows is zero and a leaf-elimination induction proves each matrix obtained by deleting one row has determinant +/-1. If rows are not allocated a_i-1 to every block, one block has too few rows and its columns are dependent in the full square matrix. If allocated correctly, the blocks are square and each determinant is +/-1. There are product a_i ways to omit the roots. Therefore
D_T(c)=sum_{S subset E(T)} c^{|S|} product_{C component of (V,S)} |C|.

The coefficient of c^{n-1} is n, as T has its unique full spanning tree. For n>=2, the coefficient of c^{n-2} is
W(T)=sum_{e in E(T)} a_e(n-a_e),
where deleting e separates T into parts of orders a_e and n-a_e. This equals the unordered-pair distance sum: each pair contributes one to the term for exactly those edges on its unique path. This is the Wiener index, not an ordered sum (the factor two is paid below).

If n>=3, the common leading terms cancel in D_T'(c)-D_T(c), and division by c^{n-2}, followed by c tending to infinity, yields W(T')-W(T)>=0. Equivalently, a negative leading coefficient would make this polynomial negative for all sufficiently large positive c. For n=2 both trees are the unique single edge, so their Wiener indices agree. For n=1 both are the unique singleton; if hitting time is defined there, its only hitting time is zero. If the source random walk requires positive degree, the literal source-defined domain starts at n>=2, and the singleton extension is conventional and earns no credit.

## 4. Pay the hitting-time bridge independently
For an edge ab in a tree, deleting ab gives an a-side A of order s. The expected time to hit b from a is 2s-1. A proof avoiding effective resistance is as follows. Root A at a, with external parent b. For a vertex v, let s_v be its descendant subtree order and h_v its expected time to reach its parent. At a leaf h_v=1. At an internal vertex with d children, the first-step recurrence, with one parent edge and d child edges, is
h_v=1+(1/(d+1)) sum_children (h_child+h_v).
Thus h_v=(d+1)+sum_children h_child=2s_v-1 by induction. These expectations are finite: from every vertex in the finite tree a fixed bounded number of steps has uniformly positive probability of reaching the target, giving a geometric tail in blocks. Thus the recurrence and strong Markov use are valid.
For any u,v, add these edge-crossing times along their unique path by the strong Markov property. For the reverse traversal, the two component sizes for each edge sum to n. Hence
H(u,v)+H(v,u)=2(n-1)d_T(u,v).
Summing over unordered pairs gives
alpha(T)=2(n-1)W(T)/n^2.
The factor is nonnegative, so W(T)<=W(T') proves exactly alpha(T)<=alpha(T'), as required. The same formula follows from the source Lemma2.1, but the derivation above independently pays that bridge.

## Failed alternative routes and adversarial self-check
The source size-transfer order decreases alpha, but a full Sidorenko-order comparison need not be generated by these transfers: no such generation lemma was supplied. Testing only complete bipartite targets controls bipartition sizes, not W. Rank-one kernels test degree moments, not all cut sizes. Neither shortcut closes the problem. The Gaussian route pays those gaps globally rather than extrapolating the source's <=8 observations.
The noninjective-map error is essential: without it, expected homomorphism counts in a random weighted graph are not exactly the naive kernel integral. The direction is checked twice: decreasing inverse-square-root determinant reverses the density inequality; the common leading coefficient is n, so the next determinant coefficient has the desired direction. Constant c, arbitrary n and all tree shapes are covered. No requirement that T and T' be distinct is used. This is self-checking, not independent review.

## Scientific gates and precise holds
Ordinary full-literal derivation: PROPOSED PASS, pending independent adversarial review.
Original source: current arXiv v4 body read; original v1 not acquired before the final denial and no later version delivery attempted.
Final source: identified DAM389 (2026)119–125, DOI10.1016/j.dam.2026.03.043, PII S0166218X26001903 returned403. Entire work is unavailable for NEW alternate deliveries, including versions/arxiv/DOI/author/cache/mirror. Existing separately acquired v4 remains documentary evidence, not proof of final equivalence.
Prior: Sidorenko1994 DiscreteMath131 pp263–277, DOI10.1016/0012-365X(94)90388-3 / PII0012365X94903883 returned403. Search identifies functional equivalence and incomparability criteria; those proof bodies remain specifically unread, with no alternate recovery. No theorem subsuming this Wiener implication has been authenticated. Csikvari–Lin Homomorphisms of Trees into a Path pp1–7 and17–19 read, including Theorem1.1 and its even-target proof, KC transformation and final questions. Its arbitrary-target star extremality and path-target results do not prove this arbitrary-pair implication. Its reference7 Graph homomorphisms between trees, EJC21(2014)P4.9 is a specific unread companion with a Wiener-based star-extremality proof claim; general-pair subsumption remains unpaid. Search snippets were not used as proof bodies.
Current registries: all four exact root GETs returned504. No heads, current statement bodies or chronology paid. Entire failed root artifacts unavailable for alternate delivery. No registry absence claim.
Novelty: NOT ESTABLISHED; bounded searches found no authenticated exact duplicate, which is not worldwide novelty.
Significance: a full arbitrary-pair necessary-order theorem would answer the exact question, rather than one family or endpoint. Strongest contrary case: the Gaussian functional test and forest expansion may already be an applicable published necessary-condition argument. It requires actual prior bodies to resolve; no routine-adaptation exclusion is asserted merely because the tools are classical.
Family: no accepted-family connection authenticated; source/topic names alone do not clear this gate.
Formal: not run; substantial analytic, probability, matrix and random-walk bridges remain implementation work. DORMANT-SOL-FORMAL-PLAN.md is a plan only.
Independent/procedure/acceptance: no independent review, no root acceptance, credit0. Access failures retained. Historical receipts are not backfilled. No generic worldwide-unknown veto was used; the named final/prior/registry deficits are concrete.
