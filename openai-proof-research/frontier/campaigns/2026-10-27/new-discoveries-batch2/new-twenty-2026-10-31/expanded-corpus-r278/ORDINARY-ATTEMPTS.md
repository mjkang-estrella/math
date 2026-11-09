# Ordinary attempts and exact exclusions

No computation, Lean execution, solver or numerical search was used. These are ordinary deductions, with source eligibility distinguished from mathematical plausibility. No candidate is promoted.

## 319097 and 319099: complete classical/source bridge

Read 0910.2013 v3 equations (5), (17), (21), Conjectures 6 and 9, and 1004.3435 Theorem 2 and proof, formulas (12)–(13). The latter is periodic and does not by itself settle the Dirichlet formulation: that distinction matters.

Let h=epsilon, L be the positive Dirichlet tridiagonal Laplacian on indices -N+1,...,N-1, X the diagonal indicator of -K,...,K, b=phi''(2F), and a=phi''(F)+4b. Directly from the source stencils,

Q = Lqcf = a L - h^2 b X L^2,
R = Lqnl = a L - h^2 b L X L.

For Q, the atomistic rows are precisely those selected by X; outside they equal aL. For R, in the interior |j|<K the fourth-difference correction is L^2; at j=K the correction h^2 LXL has coefficients (1,-4,5,-2) on (j-2,j-1,j,j+1), at j=K+1 it has coefficients (-1,2,-1) on (j-2,j-1,j), and it vanishes farther outside. Reflection gives the negative interface. This matches (21). The K<=N-2 restriction keeps the selected atomistic rows from encountering the outer fourth-difference boundary ambiguity, including K=N-2. L is positive definite since its quadratic form is the sum of squared consecutive differences with zero boundary data. Hence invertible.

Then L Q L^{-1}=R. Since R is real symmetric, Q is diagonalizable and has precisely its spectrum. For the preconditioned operators B=L^{-1}Q and C=L^{-1}R, we have L B L^{-1}=Q L^{-1}=C=aI-h^2 b XL. Also L^{1/2} C L^{-1/2}=aI-h^2 b L^{1/2} X L^{1/2} is real symmetric. Thus B and C are diagonalizable and isospectral. This does not require a>0 or b<0, although the source ordinarily assumes physical signs.

This is a complete ordinary reduction of both exact spectral statements, conditional only on their source operator definitions. It repeats the published LQ=RL mechanism with an invertible Dirichlet L, and uses elementary similarity/spectral theory. It is EXCLUDED as a complete classical/source bridge, not on grounds of proof length. No claim of a new theorem, first proof, or full journal/citation clearance. No Pi implementation justified.

## 319105: printed peanut family, exact count reconstructed

Read Hegarty v1/v2 Conjecture 1.8 and Goff, Integers 13 (2013), A42, Sections 1, 2 and 7.2. For every even d>=6, partition vertices into R1 of size d+1 and R2 of size d+2. R1 is complete except w1w2. In R2 delete uv1,uv2,uv3 and a perfect matching on R2 minus {u,v1,v2,v3}. Add only cross edges uw1,uw2.

Every degree equals d: w1,w2 have d-1 internal neighbours and one cross neighbour; u has d-2 internal and two cross neighbours; each vi loses one internal edge; each remaining R2 vertex loses its matching partner. Both induced parts are connected and joined, hence G is connected. All deleted internal pairs are at distance two. The new cross pairs at distance two are u with the d-1 vertices of R1 minus {w1,w2}, and w1,w2 each with the d-2 internal neighbours of u. There are no other new cross pairs. Thus

|E(G^2) minus E(G)| = 1 + 3 + (d-2)/2 + (d-1) + 2(d-2) = (7d-4)/2.

The square is not complete: any vertex of R1 minus {w1,w2} and any vi have distance at least three. Since n=2d+3, the new-edge ratio tends to 7/4, refuting the claimed 2-o_d(1) coefficient even for connected graphs. This is exactly the printed peanut recipe and count, not an eligible new witness. Disconnected unions of cliques also defeat the literal omitted-connectivity wording, but that correction earns no credit and is unnecessary.

## 318836: cube route collides with the printed necessary condition

Source 0908.1619 p.6 defines realizability existentially over geometric realizations with the prescribed graph, rather than separation in one fixed embedding. The p.7 footnote already states that no face subgraph may be disconnected by the cutset, with a convexity justification. Theorem 3.4 and Conjecture 3.5 are the exact target passages; the purported proof sketch is not a completed proof.

A concrete obstruction attempt uses Q4 on binary strings and
C={0000,0010,1010,1110,1100}.
Its induced path connects the whole set. All eight vertices with fourth coordinate 1 remain in the complement and form Q3; every other complement vertex has an edge into this Q3. Thus both sides are connected. In the square with third=fourth=0, C consists of opposite vertices 0000 and 1100. Their diagonal meets the other diagonal in every convex quadrilateral, so no linear functional strictly separates these pairs. C has five vertices, fewer than any cubic facet's eight.

For the fixed standard cube this is a rigorous obstruction. To refute the source's existential graph-realization reading, one must additionally prove that this designated graph square is a two-face in every 4-polytope with graph Q4 (e.g. through simple-polytope reconstruction, with a labeled graph/face bridge). That bridge has not been proved here. Even after paying it, this is just an explicit instantiation of the source's printed stronger necessary condition, not a source-independent mechanism. Do not promote the fixed-embedding obstruction as a literal refutation or give novelty credit. No full figure audit or cited-work clearance was completed.

## 318654: sustained finite algebraic route, unpaid identity

Read Karklinsky–Romik Conjecture 2, its ordinary upper-triangle Theorem 1, Fischer–Romik equation (7), Theorems 1–2 and the listed small tables in text. The extension is a signed linear combination, not an independent nonnegative ASM count. In particular its bottom row is -sum_{r=j}^{n-1} A_{n-1,r}, and its diagonal entries need not be nonnegative. A sign-based counterexample route therefore fails.

Let F(i,j) be the proposed double sum. Finite binomial expansion gives
F(i,j)=X_n(i,j)+(1-E_i)F(i,j+1),
with F(i,n)=X_n(i,n), using zero extension of the singly-refined coefficients outside 1,...,n. This supplies a concrete descending-column proof route, not a solver encoding.

The exact remaining task is to show that the DEFINED extended array satisfies
Ahat(i,j)-Ahat(i,j+1)+Ahat(i+1,j+1)=X_n(i,j)
for j<=i and j<n, with the same boundary at j=n. After substituting equation (7), this is an explicit finite binomial-coefficient convolution against the ordinary A(n,p,q), which can themselves be replaced by the proved upper-triangle formula. Neither the ordinary theorem (only i<j) nor near-symmetry alone pays this residual. Closure would require a uniform identity using the refined factorial formula and the exceptional near-symmetry terms, not a finite range test.

The lower-triangle identity has NOT been established or refuted here. Fischer 0907.0401 and later boundary-enumeration bodies have not been fully read; search hits about a different generalization do not settle this exact conjecture. No Pi task recommended until both this mathematical gap and source qualification are paid.

## Remaining records

374882: source Conjecture 1.1 is the full MMS claim. Partition averaging proves only k dividing n (a published source theorem), not n>=4k generally. No uniform route: park immediately.
318171: source equation (31) explicitly reports a proof conditional on the relevant RS conjecture. A modern RS theorem needs the correct horizontal-symmetry/boundary bridge; not proved here. Known-outcome lead, no novel-investment claim.
318172: source Conjecture 3 uses parity-adjusted half-turn link patterns, not horizontal symmetry. Total-at-z=1 agreement is only one specialization. No all-coefficient bijection or recurrence supplied.
318195: exhaustive binary representations are exponential and do not prove polynomial rank-oracle complexity. Internal four-connectivity removes the source spike example, but does not supply an oracle bound. Park.
318253: the published bounded-queue/unbounded-stack family has a fixed-depth bounded-stack subdivision. If a bound f for <=1 subdivision existed, replace it by its nondecreasing envelope. Any fixed length<=6 path subdivision is decomposable into three successive <=1 subdivisions, by balanced splitting. The threefold iterate bounds the original stack number, a contradiction. Thus the published counterfamily and an elementary iteration settle the literal k=1 version too. Attribution to Bannister–Ostergard in metadata is not the source attribution Blankenship–Oporowski. Excluded published result/complete source bridge.
318277: v1 Conjecture 5.9, v2 Conjecture 5.6. A Koda–Sato–Takegahara primary abstract reports an affirmative answer, but the body fetch failed 503 and web retrieval later returned 429; no retry/bypass. Need actual theorem with rho normalization and all k before declaring an exact proved outcome. Park with strong known-result lead. Hensel lifting without an analytic interpolation and derivative congruence is not a proof.
318498: source Theorem 2 supplies the far-from-boundary class equivalence. The all-class converse in the conjecture is not paid by that theorem; no analytic full route.
318575: exact source Theorem 16 and proof settle it; v1/v2 explicitly contain Proof of Conjecture 1. Known.
318642: source v2 Corollary 4.3 explicitly proves the descent-preserving bijection; v1 earlier corollary numbering differs. Exact count equality follows fibrewise. Known.
318685: source Conjecture 4.3 remains a uniform saturation claim, equivalent through the printed reductions to the hard remaining part of the K5-minor criterion. Planarity alone does not supply lattice-cone decomposition. No candidate hole or constructive induction.
318984: source v2 distinguishes normalized ind=1 from v1 Index=n. Its printed Lemke–Kleitman counterexamples concern longer sequences and n even, so do not refute the length-four gcd(n,6)=1 statement. No unit-scaling interval-cover proof for every composite n. Park.
319080: Ayyer–Strehl Theorem 4 explicitly proves both factorization and ratio. Read Theorem 8's triangularization argument and Proposition 7 proof. The separate geometric-eigenvector conjecture on the current registry is NOT this record. Known.
319125: source Conjecture 2 is a uniform classification, not merely the independent-set size bound. The n=1 theorem and affine-group counterexamples in the source do not settle n>=2 in PGL. No exceptional maximum set or all-dimensional proof.
319241: to refute existence of epsilon needs a family of six-cycle-free graphs with bias*n/e^(3/2) tending to zero; one finite graph with positive ratio cannot do it. The source's e^2/n^2 sufficient condition cannot replace the requested e^(3/2)/n at sparse density. No such family or uniform proof.
319247: all graphs, including infinite. A finite minimum-cardinality colouring is strongly minimal since cancellation of the common finite cover members gives |C minus D|<=|D minus C|. Infinite cardinals do not permit that cancellation. No infinite exchange/compactness argument; finite result alone not eligible.
