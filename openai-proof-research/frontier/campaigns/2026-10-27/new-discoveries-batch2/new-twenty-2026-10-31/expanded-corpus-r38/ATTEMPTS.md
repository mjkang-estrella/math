# Mathematical investigations — r38, 2026-11-01 UTC

No result is submitted for acceptance. Diagnostic computations below have no formal semantic certificate. Source hashes and acquisition times are in fetch*-receipts.json. All literal records are retained byte-for-byte with the terminating newline, and extraction records one-based chunk lines and hashes. No claim of globally new or exhaustive technical review follows from this reservation.

## 345813: pop-stack cost classification (rank 1; parked)

Read the published DMTCS paper, definitions in Sections 1.1 and 4.1, Definition 16, the full two-part wiring-diagram proof of Theorem 27, Proposition 28 with proof, and Conjecture 29. T reverses each maximal decreasing consecutive block; runs are maximal increasing consecutive blocks. A skew-layered permutation is a skew sum of identity permutations, specified by a positive composition of n. Cost is the LEAST number of iterates giving identity. The all-increasing and all-decreasing permutations are excluded. The conjecture distinguishes all even n, and the two odd-n central-run/fall alternatives. Our diagnostic interprets the size-at-least-three condition on the central monotone block; no statement-fidelity certification for a final theorem is claimed.

First mechanism: exhaust compositions, not all n! permutations. sorting_diagnostic.py checks all nontrivial compositions for 3 <= n <= 14 (16,356 total), reversing maximal decreasing blocks exactly. It also checks every two/three-part composition at n=17,25,33,45 (1,954 further cases). No discrepancy. The output is finite diagnostic evidence, not a theorem or novelty evidence.

Second mechanism: extend the source wiring-diagram argument, which describes green/orange paths in five segments when inner runs are EVEN. Its construction proves a restricted maximum-cost family already; it is not a full bridge to Conjecture 29. An odd run leaves an unpaired central path. A proof of the conjecture must control its collisions with paths from other runs; independently analyzing each run does not justify simultaneous phase timing. Proposition 28 supplies only a necessary skew decomposition for maximum cost, not its converse.

Third mechanism: induction by deleting both endpoint positions and standardizing. mechanisms.py explicitly disproves the naive cost recurrence cost(p)=cost(peeled(p))+2. For composition (1,4), costs are 4 and 0, and for (1,3,1), costs are 3 and 0. Thus an induction must retain collision/phase information absent from the composition's interior. We did not substitute a finite table for this missing invariant.

Precise remaining mathematical endpoint: establish, for every nontrivial skew-layered permutation, whether T^(n-2)(p)=id according to the specified central monotone-block criterion, and prove T^(n-3)(p) != id in the cost n-2 case. A uniform collision invariant valid for arbitrary odd inner runs is missing. Formalization then needs an actual finite-permutation operation, maximal block decomposition, iteration preservation, least-cost definition, composition-to-skew-sum bridge, and full quantifiers. No Lean endpoint was written.

Public registry check: current Omega PopStack classification/families/definitions prose and classification Lean body concern a pop stack WITH A BYPASS and a class D of sortable permutations, citing Cioni–Ferrari–Smith 2025. Read bodies are not an identical statement. This is only a bounded distinction; the truncated root tree is not absence evidence. OpenAI current complete preprint subtree path screen is recorded separately.

## 346099: strengthened spherical even-distance bound (rank 2; parked)

Read Hegedüs 2004.02240v3 in full, including the determinant/monomial proof of Theorem 1.7 and concluding Conjecture 1. The proved theorem requires paired inner products +/-a_i; the conjecture assumes only that the sum of the s inner products is nonnegative. The parity of every polynomial monomial in the proof depends on the paired-root premise. Reusing that proof without a replacement argument would silently strengthen the hypotheses.

Read Barg–Musin 0905.2423, Theorem 3's complete inertia proof, Lemma 4's coefficient proof, Theorem 5 with proof, and the spherical specialization (Theorem 15). The technique bounds size by the sum of harmonic dimensions with positive annihilator coefficients. The root-sum hypothesis controls the s-1 coefficient, not all lower odd coefficients.

Exact obstruction to that shortcut: for s=4 and ambient n=3, take candidate inner products (-9/10,1/10,3/10,1/2). Their sum is zero. The annihilator is
q(x)=x^4-(29/50)x^2+(24/125)x-27/2000.
In the Legendre basis P_0,...,P_4 its coefficients are
(-41/6000,24/125,97/525,0,8/35).
Hence the direct positive-inertia estimate retains dimensions 3+5+9=17, exceeding the proposed binomial(6,4)=15. This is an exact obstruction to the proposed coefficient-sign proof, NOT a counterexample: there is no constructed spherical set realizing these distances with 16 points. mechanisms.py computes the rational polynomial identity reproducibly.

Other attempted mechanism: use highly symmetric realizable sets instead of arbitrary roots. Paired inner-product sets already lie in the published theorem, so they cannot supply new credit. Antipodal constructions introduce -1 and a negative total root sum; translating/lifting into a hemisphere adds a dimension and changes the target binomial. These operations do not preserve a useful violating ratio by a demonstrated argument. No uncontrolled point search was launched.

Remaining lemmas: either a realizability-dependent positive-inertia reduction eliminating at least the excess odd-dimensional contribution, or an exact Gram matrix with diagonal 1, correct rank/positive semidefiniteness, exactly s distinct off-diagonal entries with nonnegative sum, and size above binomial(n+s-1,s). No such reduction or matrix is proved. A numeric Gram matrix would still need exact PSD, rank and distinct-distance bridges before Lean could refute the literal claim. No theorem-level counterexample or novelty claim.

Acquisition error retained: gerzon-barg-musin.pdf is the unrelated 0903.4774 paper; it was detected by its actual title and never used mathematically. barg-musin-correct.pdf is 0905.2423 and is the source actually reviewed.

## 346372: packing-minima transference (rank 3; parked; scope discrepancy)

Read Henk–Schymura–Xue 2005.02234 definitions (1.1)-(1.4), Proposition 1.1 and its proof, Conjecture 2.2, Proposition 2.4 and proof, and the discussion around Corollary 5.4. In this source K_c=K-K, NOT (K-K)/2 as in the cached MathDB record. This normalization is explicitly responsible for the constant 1/2. Source-paper scope takes precedence; no altered-normalization result is proposed for credit.

Write C=K-K. Source identities are rho_1(K,Lambda)=1/lambda_1(C*,Lambda*) and rho_n(K,Lambda)=lambda_1(C,Lambda). Since C* is symmetric, its difference body is 2C*. Thus the conjectured product is exactly 1/2 at j=1. At j=n the second factor is 1/lambda_1((2C*)*,Lambda)=1/(2 lambda_1(C,Lambda)), again giving product 1/2. Both endpoints are elementary consequences of the source identities, not new discoveries. The middle indices require additional work.

Attempted bridge from Proposition 1.1: multiplying the two lower bounds gives
1 / (2 lambda_j(C*,Lambda*) lambda_(n-j+1)(C,Lambda)).
Classical lower transference bounds that denominator product BELOW by 1, which puts this expression AT MOST 1/2. The inequality direction cannot supply the needed lower bound. Upper transference gives only a dimension-dependent lower estimate, not the exact constant.

Second route uses the maximum over quotient lattices (1.3). A subspace attaining one maximum need not give a complementary dual subspace attaining the other. The actual projection-polar identity in the source converts a polar of a projection to an INTERSECTION, while packing minima take PROJECTIONS. The missing lemma is a simultaneous dual flag/quotient selection theorem giving the required product uniformly; treating intersection and projection as interchangeable would be false. Box and endpoint checks are already source-level special cases. No full-scope feasible proof or literal Lean endpoint obtained.

## 346368: bicyclic Graovac–Ghorbani upper bound (stop: old source correction/prior resolution)

Read source definitions of connected simple bicyclic graphs (n+1 edges), the exact distance-count index, and Conjecture 5.2. The displayed bound has sqrt(2)/2. The graph H specified there has the following five core-edge count pairs when m=n-4 leaves attach to one degree-three vertex A of the diamond K4-e: (m+1,1) on AB, (m+2,1) twice on AC/AD, and (2,1) twice on BC/BD. Each pendant edge has (n-1,1). Consequently its index is
(n-4)sqrt((n-2)/(n-1))+sqrt((n-4)/(n-3))+2sqrt((n-3)/(n-2))+sqrt(2).
The display's sqrt(2)/2 is inconsistent with its OWN asserted equality graph. This is an excluded source-formula correction, not a new discovery.

Read Song–Liu–Ou 2308.12159's exact Theorem 3.9, its proof and preceding extremal reduction Lemma 3.8. The theorem proves the corrected bound with sqrt(2), for all n>=4, with the same diamond/leaf extremal graph. Thus corrected intended mathematics also has a public prior resolution. Later publisher PDF route returned 404; published-version proof body is not claimed read. The preprint body is sufficient to stop this route. No formalization investment.

## 346096 and 346097: Borel poset secondary review

Read primary definitions and Conjectures 1/2, Theorem 2 and proof, Lusin–Novikov statement, Lemma 4 and proof, Proposition 1 and proof, and Theorem 5. Finite-width ordinary compactness does not guarantee Borel chains. In the dual problem the rank-level sets are projections of Borel chain-existence relations; arbitrary Borel projections need not be Borel. Local countability is exactly what supplies the source's Lusin–Novikov bridge. No new unrestricted Borel bridge is proved; both are parked. No formalization.
