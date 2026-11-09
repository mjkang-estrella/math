# Full-scope attack: unresolved

No result nominated. Root alone accepts/counts; baseline remains 9 additional / 39 total / next 40. No Lean or manuscript is supplied.

## Exact target and source screening

Li–Ling–Sun–Zhu, *Proofs and disproofs of some conjectures on zero-sum problems of new types*, arXiv:2610.19965v1, Question 3.1, printed p15 (text line771), asks whether w_r(n)=2r(n−1)+1 for every r≥1 and integer n>1. Definition (1.2), printed p2, quantifies over integer r-vectors each nonzero modulo n, and requires a nonempty selected sum zero modulo n but **not** zero modulo n². Congruences are coordinatewise; the latter requires at least one coordinate not divisible by n². Arbitrary lengths of selected subsets and arbitrary lifts are permitted.

Actual bodies read: definition (1.2), Lemma3.1 with proof (p6), Theorem1.2 (p3), its composite propagation proof pp13–14, Question3.1 and Lemma4.1 proof (p15), and Corollary4.1 proof (p16). The signed basis construction is public; rank one for all n, binary modulus for all ranks, and rank two n=2^k3^l p are public. These are not discoveries. Letzter–Morrison2306.09033v2, Theorem2.1 and proof pp4–6, gives h_p(r)≤(p−1)r(log_2 r+1), using matroid packing and additive bases. Its actual proof does not give the conjectured linear bound. Reduced sequences can contain zero sums, as [1,-1] in Z3 shows.

Before mechanism investment, 326 inherited, hash-verified cached .tex theorem/proof bodies were read and screened for zero-sum objects and author/source terms. Fourteen bodies had lexical hits; their retained contexts concern zero summands, analytic zero sums or group-presentation relators, not this lifting threshold. The criterion/embedding relators in the Kaplansky manuscript do not quantify over arbitrary admissible sequences modulo n². This is a bounded semantic screen, not a complete registry search. See cached-body-screen.json and checks.stdout. The immutable registry revision is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (2026-10-08). No current registry head is asserted.

Fresh guarded primary API checks, timestamps in access.jsonl, return target v1 and only two entries for the title-phrase successor query: Sun2606.18234v5 (published June16, updated July2 2026) and Li et al.2610.19965v1 (published/updated October14 2026). Both full bodies already frozen by r277. This verifies no newer version in that bounded query, not absence of differently titled successors. Historical inaccessible intervals stay parked. No denied routes were retried. Source hashes, exact local immutable paths and original/copy checks are in source-bindings.json and the inherited source-access-bindings.json.

## Mechanism 1: universal incidence/carry separation

Choose canonical residues a_i in {0,…,p−1}^r, all nonzero, and write lifts a_i+p b_i. Let Z be all nonempty Boolean masks I with sum_I a_i=0 modulo p. Define c_j(I)=(sum_I a_ij)/p modulo p. A bad lift exists **if and only if**, for each j, the system M b_j=−c_j is consistent, where M_Ii=1_{i∈I}. This is exact: divide every residue-zero selected sum by p, and require it vanish modulo p again. Subsets outside Z never qualify for the source target.

Thus a certificate consists of λ_I in F_p with sum λ_I 1_I=0 but sum λ_I c_j(I)≠0 for some j. It excludes every lift of these residues. Gaussian elimination with retained row combinations supplies independently checkable certificates. The new checks use three structured rank-three lists, not another random census: signed extremal plus a mixed column; all thirteen normalized projective directions; and an alternating sign change of those directions. Certificates have 4,5,5 supporting zero-subsets respectively. Each certificate is checked against all columns, and its nonzero carry pairing is recomputed directly from integer sums. Exact masks and coefficients are in diagnostics.json. No structural theorem bounding such dependencies for arbitrary input emerged.

## Mechanism 2: Boolean polynomial degree obstruction

Work in B=F_p[x_1,…,x_N]/(x_i²−x_i). Each function on {0,1}^N has a unique multilinear polynomial, with coefficients computed by Boolean Möbius inversion. Set L_j=sum_i a_ij x_i and D=product_j(1−L_j^(p−1)). D is the exact indicator of residue-zero masks, including the empty mask. In B, deg D≤r(p−1).

Define C_j(x) as the coefficient of t^p in product_i(1+x_i((1+t)^(a_ij)−1)). For Boolean x this is binomial(sum_i a_ij x_i,p) modulo p, which equals floor((sum_i a_ij x_i)/p) modulo p by the base-p binomial identity. Every selected factor has t-degree at least one, so deg C_j≤p. Therefore F_j=D C_j is the function equal to carry on residue-zero masks and zero elsewhere, with deg F_j≤r(p−1)+p. F_j(0)=0.

If a bad lift exists, F_j=−D sum_i b_ij x_i as functions, hence in B. Consequently **deg F_j≤r(p−1)+1**. A coefficient above that threshold is a sufficient obstruction. This is a proved diagnostic implication, not a proved universal degree lower bound.

For an explicit incidence identity, choose a nonzero coefficient [x_T]F_j of maximal degree d>r(p−1)+1, and S=[N]\T. Put λ_I=(−1)^|I| 1_{S⊆I} on the residue-zero masks. Pairing any Boolean polynomial H with this alternating weight extracts (−1)^N times the sum of its coefficients on masks U containing T. For H=D x_i all coefficients vanish there by degree. For H=F_j the only possible nonzero such coefficient is [x_T]F_j, by maximality. Thus this λ is a valid carry contradiction. This explains and checks a symbolic family of incidence identities.

All three length13 diagnostics have degrees (9,9,9), exceeding the threshold7. Their polynomial certificates use multipliers of degree4, and 26,18,22 zero-subset rows. The length12 signed extremal control has degrees (7,7,7) and no certificate; its actual signed integer lifts are verified against every one of its 4095 nonempty subsets. No counterexample to Question3.1 is produced.

The unweighted alternating identity and the first few low-degree multipliers cannot suffice by themselves. For N=13,r=p=3, deg F≤9, so pairing with a multiplier of degree≤3 always vanishes; deg(D x_i)≤7 makes incidence pairings vanish through multiplier degree5. The useful window starts at degree4, exactly as the diagnostics exhibit. Merely invoking Chevalley–Warning or the constant alternating sum loses the carry signal.

The missing step is a universal lower bound on at least one deg F_j, or a more flexible separator when that degree test fails. We have neither proved such a bound nor shown it necessary. If residues lie in a proper subspace, one should first use their intrinsic rank and a change of basis; the displayed ambient-rank degree bound can otherwise be unnecessarily weak.

## Structural decomposition and the composite bridge

For prime p, a direct-sum partition of the residue support into positive-dimensional subspaces permits rank induction **conditional on the prime conjecture for those lower ranks**. Lift a basis change to a matrix invertible modulo p², and project each component block onto its own coordinate summand. A bad original sequence gives a bad projected block: a projected sum nonzero modulo p² would also be nonzero in the whole vector. The projected terms remain nonzero modulo p. Therefore each block has length≤2d(p−1), and summing dimensions gives the bound. This reduces a putative minimal-rank counterexample to connected spanning vector-matroid support; it does not establish the connected case. It is a routine conditional reduction, uncredited.

A sufficient full composite bridge can be stated precisely. Let P(r,p,k) mean: every integer-vector sequence nonzero modulo p of length at least p k+(2r−1)(p−1) contains k pairwise disjoint nonempty blocks whose sums are zero modulo p and nonzero modulo p². P(r,p,1) is exactly the prime endpoint. The assertion for all k is stronger; prime success alone does not establish it.

Assume P(r,p,k) for all primes and positive k and assume the target bound at t>1. Suppose A is admissible and bad modulo pt, with length 2r(pt−1)+1. Set k=w_r(t)=2r(t−1)+1; then |A|=p k+(2r−1)(p−1). Terms zero modulo p form q singleton blocks. If q≥k we already have k blocks. Otherwise remove them. Remaining length is at least p(k−q)+(2r−1)(p−1), so P supplies k−q additional blocks.

For every block put c=σ(block)/p. A singleton gives c≠0 modulo t by original admissibility. A nonsingleton good modulo p block also gives c≠0 modulo t: otherwise its sum would be zero modulo pt and original badness would force zero modulo (pt)², contradicting nonzero modulo p². The k vectors c are bad modulo t, since any union summing to zero modulo t has original sum zero modulo pt, hence zero modulo p²t²; dividing by p implies zero modulo t². This contradicts w_r(t). Induction over prime factors, including repeated factors, would then prove the full question. This is a complete conditional bridge, not a proof of P. It reproduces the architecture of the authors' public rank-two propagation and is not credited as new.

The tempting greedy proof of P by always taking a block of length≤p fails already at its first step. In F3^4 use two copies of each of the nine vectors (1,x,y,x²+y²), x,y∈F3, and remove one copy, leaving17=2·4·(3−1)+1. There are no residue-zero subsets of length1 or2 by the first coordinate. A zero triple in the graph of x²+y² must have three equal parameter pairs: if u+v+w=0, the quadratic sum equals −Q(u−v), and Q(z)=z_1²+z_2² is anisotropic over F3. Hence u=v=w, unavailable with multiplicity≤2. Exact checks enumerate every subset through size6 and confirm no zero triple. This is a counterexample to the short-block shortcut only; the list has longer zero subsets and is not a certified bad lift. It leaves P unresolved.

## Disposition

HOLD: the universal incidence separator, or a sufficient universal polynomial degree theorem, and the multi-block composite packing theorem remain missing. Nothing here qualifies as a new full-scope outcome. Preserve current-registry uncertainty and do not formalize, write a manuscript, or count the finite certificates or conditional bridges.
