# Ordinary routes and precise residuals — zero credit

No mathematical computation, enumeration, solver, Lean implementation or dispatch was performed. All calculations below are handwritten algebra. None of these routes currently supports a new source-qualified endpoint.

## 357560 — arbitrary total lifetime

Literal endpoint: independent stationary copies of a finite irreducible, aperiodic reversible chain with common transition matrix P satisfy E|union R_i(t_i)| >= E|R(sum t_i)| for arbitrary positive integer lifespans, including odd sum. The source's Assumption I and Theorem 1.1 supply the actual hypotheses; its proof counts times 0 through t. Do not change to arbitrary nonstationary starts or lazy chains.

Source reduction read: for each excluded vertex y, let Q_y be P restricted to V minus {y}, and let s_y(t)=Pr_pi(tau_y>t). Detailed balance symmetrizes Q_y as A_y = D^(1/2) Q_y D^(-1/2). With u=(sqrt(pi(x))) outside y, s_y(t)=u^T A_y^t u. In particular s_y(0)=1-pi(y). Independence gives the exact desired inequality

    sum_y product_i s_y(t_i) <= sum_y s_y(sum_i t_i).

This is the full endpoint, not merely a spectral proxy. The source proves the stronger pointwise product inequality when the total is even by pairing odd moments and then using even moments. With an odd total, pairing leaves one unpaired odd exponent. The covariance of x^(2a) and x^(2b+1) need not have a sign on [-1,1]. Thus repeating Chebyshev on signed eigenvalues is invalid.

Attempt 1: odd pair reduction. Pair all but one odd lifespan. This leaves precisely the mixed-parity inequality s_y(2a)s_y(2b+1) <= s_y(2a+2b+1), possibly with the source's stronger factor 1-pi(y). No proof of that mixed inequality is obtained. Pairing is a valid simplification, not a completion.

Attempt 2: add one step to the odd lifespan, apply the even-total theorem, then remove it. Writing s(t)-s(t+1)=h(t), both sides change. The even theorem bounds product s(t_i+delta_i) against s(T+1); the needed correction compares h(T) with h(t_j) times all other s(t_i). Monotonicity alone gives neither this comparison nor its sum over y. Time reversal identifies finite path weights but does not supply this correction bound.

Attempt 3: use classical walk inequalities to refute the pointwise spectral step, then embed. The primary proposers' solution to Problem 83-15 (Lagarias–Mazo–Shepp–McKay) is identified in Klamkin's collection: the ordinary symmetric walk-product inequality has mixed-parity counterexamples. The downloaded book is only a 15,000,000-byte prefix, pdftotext exit 1: the actual counterexample construction is NOT reviewed. More importantly even a complete such counterexample would not solve this MathDB claim. A killed-chain realization must have a nonnegative substochastic Q with detailed balance, a full stochastic extension P, correct stationary mass at y, irreducibility and aperiodicity, and a strict violation after summing over EVERY target y. Arbitrary symmetric-matrix moment failure pays none of those bridges. No exact in-scope chain is supplied.

Precise residual: prove the aggregate displayed inequality for all these chains, or give a fully specified admissible chain and lifespans with exact aggregate reversed inequality. Source qualification also remains blocked by the identified 2025 journal body (403, no retry). The author page links only the arXiv version. Latest arXiv history lists only v1, 28 February 2023. No Pi plan.

## 357762 — cooperative painting for different matroids

The primary paper's Theorem 2 proves an OFFLINE list coloring theorem: k-colorable matroids N_i and lists L(e) of size k admit f(e) in L(e) with each fiber independent in its own N_i. The proof uses the union rank formula and the inequalities r_i(X intersect E_i)>=|X intersect E_i|/k, together with sum_i |X intersect E_i|=k|X|. I read this rank mechanism and the exact Section 3 Conjecture 1, as well as the Lasoń–Lubawski companion's Lemmas 1–2 and Theorem 3 proof.

Attempt 1: apply the offline theorem to the final offers. It supplies an assignment after ALL offers are known, but that assignment can disagree with Ann's earlier irrevocable choices. The quantifiers are different: for every complete offer history there exists a coloring does not imply there exists an online strategy against every adaptive history. Thus offline feasibility is a helper only.

Attempt 2: transport Lasoń–Lubawski's moving-cover proof. For one matroid, their exchange Lemma 2 moves elements along a cover I_1,...,I_k and colors an independent set I in the offered set V, reducing the remaining list sizes for V. Each exchange preserves independence because BOTH exchanged sets belong to the SAME matroid. With independent sets in different N_i, the required unrestricted exchange principle is actually false, even for 2-colorable partition matroids. Here is a handwritten exact obstruction. On E={a,b,c,d}, let N_1 have capacity-one blocks {a,c} and {b,d}, and let N_2 have capacity-one blocks {a,b} and {c,d}. Let I_1={a,d}, I_2={b,c}, and X={a}. Both initial sets are independent in their respective matroids. Any Y subset I_2 for which (I_2 minus Y) union X is independent in N_2 must contain b, since otherwise a and b share its first block. But then (I_1 minus X) union Y contains b and d, which share the second block of N_1, so it is dependent. Thus no Y works. Each matroid is 2-colorable: N_1 by {a,b},{c,d}, and N_2 by {a,c},{b,d}. This refutes the transported exchange lemma. It does NOT refute the painting conjecture, because an actual strategy may use a different invariant and choices.

Attempt 3: maintain a robust rank invariant for residual offers. For any fixed future availability sets E_i, a residual set U is colorable iff |X|<=sum_i r_i(X intersect E_i) for every X subset U. Ann would need to choose I subset B independent in the CURRENT matroid such that those inequalities remain valid for every future completion consistent with the per-element offer budget. The offline proof handles one fixed tuple (E_i), not their adaptive universal quantifier. No uncrossing argument establishing a single I for all tight X and all completions is proved. Greedily choosing a current basis has no shown rank guarantee for the other matroids.

Semantic caution: the source wording says elements are picked 'at most k times' and finishes in at most t rounds. Literally allowing Ben never to offer an element makes even the source's asserted equal-matroid case fail. The companion explicitly ends when all lists have k entries. I do not promote the omission of this ordinary painting convention into a discovery or silently claim a strategy for an ambiguous game. A source-faithful formal endpoint needs the legal-offer/losing rule fixed by the painting convention.

Residual: a full strategy preserving an appropriate adversarial invariant, or a legal adaptive offer tree refuting it, with all matroid and game conditions. No certified obstruction or full proof is supplied. No Pi plan.

## 358005 — coefficientwise Gaussian product

Put N=a+b and [n]!=product_{j=1}^n (1-q^j)/(1-q). Let D=[a choose k]_q[N choose b-k]_q-[b choose k]_q[N choose a-k]_q. Exact factorial cancellation gives

    D = [N]! / ([k]![a-k]![b-k]!) * ([a]!/[a+k]! - [b]!/[b+k]!).

Equivalently D is exactly the second rational expression in the literal record, because multiplying [a choose k][b choose k][N choose b] by 1/[a+k choose k] gives the first product and the other reciprocal gives the second. This establishes equivalence in Q(q), not coefficient positivity by cancellation of inequalities.

Attempt 1: rectangular partition injection. The RHS counts pairs of partitions in k by (b-k) and (a-k) by (b+k) boxes, by total size. The LHS uses k by (a-k) and (b-k) by (a+k) boxes. The total degree difference is 2k(b-a), so the target has adequate degree, but moving cells from the wider first rectangle into the second can violate partition order. No reversible area-preserving transfer is specified. The easier inequality [N choose b-k]>=[N choose a-k] (the source's Butler/Andrews discussion, and a 2022 public MO answer) does not survive multiplication by the smaller factor [a choose k].

Attempt 2: partial fractions, using journal Lemma 16 (arXiv Lemma 8). For 0<q<1 all summands in the reciprocal-difference formula are nonnegative. This gives pointwise nonnegativity in that real interval. Each factor (1-q^j) has a negative coefficient, however; clearing denominators with Gaussian factors does not make each resulting summand coefficientwise nonnegative automatically. The exact missing lemma is a nonnegative polynomial decomposition or a coefficient-preserving injection, including all cancellation terms. The journal's examples for k=1,2,3 were read, and do not fill that lemma.

Attempt 3: adjacent-parameter induction in b. The q-Pascal recurrence creates positive shifts of differences with changed a,k together with unmatched boundary terms. No closed induction invariant for those boundary terms was found. Even k=1 leaves

    D = q^(a+1) [a][b][b-a]/([a+1][b+1]) * [a+b choose a]_q.

This identity follows from [b+1]-[a+1]=q^(a+1)[b-a]. Its visibly positive real factors still do not prove coefficient positivity of the rational product. k=0 is equality but is not the general endpoint.

The full journal final Section 4, Lemma 16, Examples 17–18 and related Lemma 20 were read. The 2026 Amdeberhan–Beck preprint explicitly treats q=1 generalizations, not this full product claim; only its introduction was reviewed. The original arXiv history has v1 only. No correction or complete citing-body sweep is claimed. Residual: prove D has nonnegative coefficients for every integer 0<=k<=a<b, or give an exact negative coefficient with a handwritten coefficient certificate and full source check. No Pi plan.
