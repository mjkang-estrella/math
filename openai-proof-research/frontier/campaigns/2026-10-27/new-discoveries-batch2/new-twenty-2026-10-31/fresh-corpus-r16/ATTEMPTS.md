# Sustained routes and exact stopping points

No discovery credit is claimed. None of the routes below supplies a new full-scope ordinary theorem with a literal Lean endpoint.

## 336116 — powerful sets: exact search, induction, and predecessor closure

Original arXiv1705.07437v1 Conjecture3.8, p7: S⊆F₂ⁿ, n≥2, |S|=2^(n−1), and every zero-coordinate restriction count is a power of2. Seek a coordinate deletion that is a bijection onto F₂^(n−1). The published2018 version was also downloaded; later Jones uses different numbering for the same source conjectures.

For integer bitmask x, let b_x indicate membership of x in S. For each coordinate-mask Z, the exact powerful condition is

    sum_{x & Z = 0} b_x = 2^k_Z,  0 ≤ k_Z ≤ n−popcount(Z).

One-hot variables choose k_Z. Fix b_0=1 and sum b_x=2^(n−1). Failure of the conjecture means that for every coordinate j there is an x with x_j=0 and b_x=b_(x xor 2^j)=1. Introduce binary y_(x,j)≤b_x,b_(x xor 2^j), and require sum_x y_(x,j)≥1. No reverse AND constraint is necessary for feasibility. With fixed half-cube size, deletion is onto iff injective, and failure of injectivity is precisely such an edge. These are semantic bridges, not a solver-based proof.

The n7 model had1144 variables and1159 constraints; HiGHS exhausted90 seconds with no primal solution and no infeasibility certificate. This establishes neither truth nor falsity, even at n7. The n8 run was terminated when direct predecessor evidence arrived. The reproduction script can generate the models, but further discovery investment is unwarranted.

The ordinary induction route contracts a coordinate (its zero slice remains powerful), then tries to lift a deletable element of the smaller half-cube. A coloop complicates the lift: deletion can collapse pairs rather than stay injective. This is exactly handled by the actual successor, Jones arXiv2009.09616v1, not an unresolved new lemma:

* Definition in Section2: a star e means S={X:X∈T}∪{X∪{e}:X∉T} on the remaining ground set.
* Theorem4.3, pp6–9: an order-n rank-(n−1) powerful set has a deletable element. Its minimal-order proof splits off a unique high-rank coordinate or uses singleton-rank-one contractions; the eight-fiber tables and zero-count identities identify complementary fibers. Full selected proof was read.
* Proposition4.4, p9: such a set contains a star. If the deletable element is not a coloop it is a star; if it is a coloop, induction supplies a star and coloop/star extensions commute. Full proof read.
* Exact bridge: ∅∈S and rank(E)=log₂|S|=n−1. For a star e and each X⊆E\{e}, exactly one of X or X∪{e} is in S. Thus deletion is bijective, precisely the MathDB conclusion, including nonlinear sets and every n≥2.

Disposition: known result, zero credit. Do not send this to formalization as a new candidate. This supersedes the stale open/search summary. Theorem4.3 alone must not be cited without the coloop-to-star step.

## 336130 — uniform central appendages: exact reduction and failed extension

Read definitions, construction, necessity and sufficiency in arXiv1705.07982v1 and the actual2020 EJGTA8(1),157–180 body. Published Conjecture1 p178 still asserts A_ucg(K_n,P)=2 for radius(P)=diameter(P)=3; Section3 assumes n≥2. The n1 omission in the database would merely be a domain correction and earns no credit.

Published Proposition3.1 bounds A between κ and κ+1 for κ=cov_A(P). Theorem3.1 (preprint Theorem3.3) says A=κ iff cov_AB=κ. Proposition5.1 gives κ=2 for diameter≥3. Therefore the actual open task is a two-member cover of V(P) satisfying:

A: for each member P_i there is p outside P_i whose distance to every vertex of P_i is≥2.
B: for every p∈P_i, either some p' outside P_i has d(p,p')≥3, or d(p,P_j)≥2 for the other member j.

Any cover satisfying A/B can be shrunk to a partition: assigning each overlap vertex to just one member enlarges each complement, increases distances to the other member, and removes membership obligations. Thus both conditions persist; witnesses for A keep their distances. Neither member becomes empty because its opposite A-witness must lie in it. This justifies exhaustive bipartition checking on a fixed graph.

For a partition A⊔B, let F(v)={w:d(v,w)=3}. B is precisely: for every v, either F(v) meets the opposite part, or v has no neighbor in that part. A requires one vertex in each part with its entire closed neighborhood in that part. The script implements exactly these two conditions after computing all distances, restricted to eccentricity3 at every vertex. Seed336130 generated39002 graphs/cycle controls, of which146 had the required eccentricities, at orders6–18. Every eligible graph admitted a valid partition. This sampled support is not a proof, nor an exhaustive labeled-graph result.

Second route: adapt published Proposition5.2, which starts with distance-four vertices a,b and fixes P1=N[a], P2=N[b], then adds a vertex opposite an existing distance-three witness, or adds a new distance-three pair. For distance four the initial vertices already have opposing distance-three witnesses. For distance three this fails. The reproducible adjacency and complete distance matrix in appendage-greedy-obstruction.json have a=5,b=0, d(a,b)=3, N[a]={2,5,6}, N[b]={0,3,7,8}. Vertex6 has distances2,2,1,1 to the latter set, and hence no initial distance-three witness there. Its only distance-three vertices are1 and9, both initially unassigned. This is an obstruction to that unchanged proof invariant, not a counterexample to the conjecture (a later assignment can repair it).

Third route: maximize the cut in the graph F of distance-three pairs, while fixing these neighborhoods on opposite sides. Every unassigned vertex with no opposing F-neighbor can be flipped to increase the cut (since min-degree(F)≥1), but fixed vertices cannot be flipped. Their required opposing witnesses may themselves be fixed by other constraints or needed on a conflicting side. No simultaneous extension theorem preserving all fixed-vertex obligations was proved. Conversely, no self-centered graph forcing inconsistency was constructed. This is the precise remaining lemma; a maximum-cut assertion without fixed-vertex control is insufficient.

No Lean file asserts either the unproved extension lemma or the MathDB conjecture. A full candidate would additionally formalize graph distances, radius/eccentricity, the actual appendage minimization over all extensions and both directions of the published covering bridge; an abstract two-coloring lemma alone is not the endpoint.

## 335597 — even-column tableaux: exact coefficients and nonclosing inequality route

Read actual definitions in1703.06382v1 Section1 and Conjecture3.8, and original Bóna–Lackner–Sagan1511.08653v1 Conjecture4.3 and Theorem4.4. By Robinson–Schensted, ℓ^Θ_(n,k)=Σ_(λ∈Θ,λ₁=k)(f^λ)². Even column lengths mean rows occur in equal pairs: λ=(μ₁,μ₁,μ₂,μ₂,…), μ⊢m, n=2m. For odd n all counts vanish. The finite script enumerates partitions μ, evaluates every hook product in integer arithmetic, and sums squares, for every even n2–80. No negative log-concavity difference appears. This merely reproduces the original paper’s explicitly stated checked range≤80, not a new result.

A stronger Schur-positivity analogue is already false in the immediate source at n10; it cannot be silently used to prove this conjecture. The published double-hook log-concavity theorem covers a subset of shapes. Adding log-concave sequences does not generally preserve log concavity: (1,1,1)+(1,10,100)=(2,11,101), whose middle square121<202. Thus shape-wise or special-family log concavity does not bridge to the literal sum without a synchronized-ratio or injection argument.

A sustained endpoint calculation does simplify one inequality. For m≥5, k=m has the single shape(m,m), k=m−1 has(m−1,m−1,1,1), and k=m−2 has exactly(m−2,m−2,2,2) and(m−2,m−2,1,1,1,1). Dividing f by Catalan_m gives

    r1=m²(m−1)/(2(m+2)),
    r2a=(m−3)(m−2)²(m−1)/12,
    r2b=m²(m−2)(m−1)²(m+1)/(24(m+2)(m+3)).

The required gap at k=m−1 becomes r1^4−r2a²−r2b². Its numerator after the positive factor (m−1)²/[576(m+2)^4(m+3)^2] is

    P(m)=31m^12+144m^11+74m^10−432m^9−1569m^8
         +13160m^6−50576m^4+101376m²−82944.

P(5+t) has all positive coefficients (recorded by endpoint_algebra.py). This provides an elementary boundary inequality after hook-formula justification, not the whole conjecture: k may grow arbitrarily far from m, with an unbounded collection of paired shapes. It is an uncredited helper/parameter-range calculation and not Lean-complete. No uniform injection between the actual tableau-pair products, total-positivity theorem, or synchronized-ratio comparison for the interior was found. Full original published-body comparison beyond the inspected arXiv versions was not completed, so novelty is not cleared even for this helper.

## Source-direction traps excluded

336323: actual Section1 defines e_q as max_F|V(F)|, while the literal record calls it a minimum. For standard P² over F₂ and degree1, X0 has3 zeros, whereas the literal right-hand side is min(7,2+1)=3; this example does not separate them because all linear forms have3 zeros. At degree2, X0² still has3 zeros but the right side is min(7,4+1)=5. This is a trivial min/max wording counterexample, explicitly uncreditable; the intended maximum problem is not solved here.

335752: any n-vertex tree has at most n(n−1)/2 pairs, each at distance≤n−1, hence W≤n(n−1)²/2 and the interval length≤that+1=O(n³). This literal upper bound needs no new mechanism. Do not equate it with the intended stronger asymptotic density results or overlook the odd-n parity convention.

335942: the fetchedv1 contains SO(n)-Haar normalized-trace factorization Proposition2, with its averaging proof in the appendix. A general arbitrary-subgroup assertion cannot be substituted for it; no matching conjecture passage was authenticated. No novelty or full source review claimed.
