Raw Factory Opus delivery — UNREVIEWED, not endorsed. Task node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h020-public-signal-construction-factory-opus-20261008-r1

# H020 independent report: constructive observables and operators

I found no mechanism that survives this lens with a credible path to beating square-root work. Verified improvement stays **NONE**, and the best supported work is still the accepted square-root reference with known automorphism constants.

Two paper results from this pass could change how the root ranks open work:

- **R1** is a simple reduction from random 3SUM to elliptic-curve 3-list detection. Under the stated scope, it deprioritizes the open SP3 detector, H019's multi-query resultant, the truncated norm and Singer-convolution detectors.
- **R2** is an exact theorem. Coordinates in which translation by G acts linearly must have dimension at least k′ = ord_q(p), the MOV embedding degree, before they reveal anything about k. This explains the cost of q in the H013 Lang and normal-basis construction, and it limits translation-operator and Koopman-style ideas.

I made no edits, runs, child agents or commits. I did not read other H020 proposals; I deliberately skipped `hypotheses/H020-independent-candidates.md`. Notation: A_i, B_j, C_l are the three point lists; s is a detector's success probability; δ is a filter density.

---

## Card 1 (rank 1): a 3-list detector on random lists would solve random 3SUM

**Exact operation.** Fix E/F_p with #E(F_p) = q prime and a generator G. Let 𝒟 be any detector that:
- takes three lists of n points;
- may also be given the scalar logs of any of the lists;
- outputs a signed witness ±A_i ± B_j ± C_l = O, with success probability s on lists of independent uniform nonzero points;
- runs in time T(n).

Build a solver 𝒟′ for signed random 3SUM mod q:
1. Take independent uniform nonzero residues a_i, b_j, c_l in Z/q.
2. Compute A_i = [a_i]G, B_j = [b_j]G, C_l = [c_l]G with 3n scalar multiplications, O(n log q) group operations.
3. Run 𝒟, passing any requested logs, since 𝒟′ knows all of them.
4. Check the witness in Z/q.

**Why the reduction holds.** All four properties the root required in H017-SP3-disposition are preserved:
- **Field:** it is the same curve.
- **Conic admissibility:** the inputs are actual rational points.
- **List distribution:** independent uniform scalars give exactly independent uniform nonzero points, which are all affine.
- **Exponent:** the overhead is n log q.

Witnesses correspond one-to-one, including all four sign patterns. The 4n³ count of signed equations matches Sol's SP3 count. Target labels do not affect the point distribution, so the useful-coefficient condition plays no part here.

**Consequence.** Take a detector costing O(n^{3/2−ε}) at n ≍ q^{1/3}, the SP3 cost gate. It would give signed random modular 3SUM at critical density in O(n^{3/2−ε} + n log q) time.

The Dinur–Keller–Klein abstract states the average-case 3SUM conjecture: for r random numbers of order r³, finding a solution takes about r^{2−o(1)} time. Signed and modular variants are standard analogues, but I have not verified that they are equivalent to it.

**Scope.** Covered:
- SP3 with independent uniform lists;
- H019's multi-query resultant over three lists;
- the truncated norm;
- Singer convolution;
- slope grouping;
- any detector, implicit or algebraic, that works on independent uniform lists, even with known logs on some lists.

Not covered:
- adaptive or walk-generated lists, such as rho;
- structured known-log lists such as arithmetic progressions, where the Z/q version is easy, consistent with BSGS existing;
- four or more lists (see Card 2);
- preprocessing or advice, and multi-target amortization.

This is a conditional, problem-specific reduction. It is not a universal impossibility claim.

**Prior art and access limits.**
- Dinur–Keller–Klein, [arXiv 2111.00486](https://arxiv.org/abs/2111.00486): I saw only the first abstract sentence.
- Bouillaguet–Delaplace–Fouque, ToSC 2018 (3XOR): title and abstract only.
- Dietzfelbinger–Schlag–Walzer, [arXiv 1804.11086](https://arxiv.org/abs/1804.11086), subquadratic 3XOR by polylog factors: abstract only.
- I could not check whether Dinur–Keller–Klein bound the dense regime (larger n) for k=3 at about √(range). If they do, no label-blind 3-list detector on random lists of any size beats √q by a polynomial factor, conditionally.

**Costs.** Conversion is 3n scalar multiplications. No setup or memory beyond 𝒟 itself.

**Unsupported assumption.** Hardness of the modular, signed, uniform form of average-case 3SUM.

**Cheapest decisive falsifier.**
- The root checks the distribution identity, which takes one paragraph.
- Then the root reads Dinur–Keller–Klein's statement for k=3, modular versus integer.
- A published algorithm solving random modular 3SUM at critical density in about n^{1.5} or better would remove this barrier.

**Verdict.** This is a paper result, pending root verification. If accepted, the open SP3 detector requirement should be recorded as conditionally 3SUM-hard for random lists.

---

## Card 2 (missing mechanism): four-list merge with an "approximate order" filter

This is the only list-relation shape Card 1 does not block, because its Z/q version runs below square root.

**Positive mathematical reason.** For a prime modulus q, which has no nontrivial quotient group, the four-list problem still takes Õ(q^{1/3}). This is a self-contained version of Wagner's idea:
1. Use four lists of size n = q^{1/3}.
2. Level 1: find all pairs whose sum lies in a centered interval S of length q^{2/3}. Sort L2 and do one range query per a1, because {a2 : a1 + a2 ∈ S} is an interval. About n pairs survive.
3. Level 2: two sums in S cancel only exactly, since |s + s′| < q. So use an exact hash collision among n entries, which succeeds with probability about n²/q^{2/3} = 1.

This corrects the scope of H001-opus-critic's "Wagner needs a homomorphism, so this is ruled out outright". The real requirement is a filter whose translates can be searched by key, not a quotient.

**EC operation if the filter existed.**
- L1 holds labelled points α_iG + β_iQ; L2, L3, L4 are independent known-log lists.
- Level 1 enumerates pairs with P1 + P2 ∈ S, where S has density about q^{−1/3}. Level 2 finds an exact x-coordinate collision.
- Recovery combines labels, rejects β = 0, and verifies the scalar.
- Cost would be Õ(q^{1/3}) time and memory, plus verification.

**Requirement.** A cheap key K and a set S such that, for every point P, the set {B : P + B ∈ S} can be enumerated from an index of L2 in polylog time plus output size.

**Candidates checked on paper:**
- **(a) S = {x < B₀} with key K = x.** The set is the image of an interval under the degree-2 addition correspondence, so it has no interval structure. The polynomial route, ∏_{z<B₀} S3(u_P, V, z), has degree 2B₀ ≈ 2p·q^{−1/3}, far larger than n.
- **(b) S = {x ∈ c·μ_m}.** The per-pair test is O(log m) using Lucas sequences on the S3 roots in z. But enumerating per P still means evaluating at all n candidates, so the total is n².
- **(c) Singer-log intervals.** Translation is not affine in Singer coordinates, and it needs paid finite-field logs (H017 already covers this).

None works. If K were order-based, with K(P+B) ≈ K(B) + F(P) mod 1 on a positive-density set, K would be an approximate log phase, which is the open signal problem. An algebraic enumerator not based on order is not excluded, but none is specified.

**Prior art.** Wagner, CRYPTO 2002, from memory and not re-read. The algorithm above is self-contained. It overlaps H005-grok's m=4 cell, which framed this as an index-calculus existence tester.

**Unsupported assumption.** A translation-searchable pair (K, S) exists.

**Cheapest falsifier.** For any proposed (K, S), use a toy prime-order curve with q around 10³ to 10⁴ and random points P. Count the maximal K-runs of {B : P + B ∈ S}.
- Enumerability needs polylog runs.
- Random-like behaviour gives about |S|(1−δ) runs.

The candidates above already fail on paper.

**Verdict.** Missing mechanism. Keep it as the precise target shape, plus the H001 scope correction.

---

## Card 3 (killed by exact theorem): coordinates where translation is linear

**Hoped mechanism.** In the multiplicative group, translation by t is the linear substitution X ↦ tX, so ∏(X − t·g^l) = t^n·Φ(X/t): one precomputed polynomial serves every translate. The hope was an elliptic analogue that makes translate norms ∏_l(X − x(T + lD)) cheap for all T, to speed up arithmetic-progression and resultant queries.

**Theorem (scoped, with elementary proof).**
- Let φ: E → P^N be a nonconstant F_p-rational map given by a subspace V ⊆ H⁰(E, L), with deg L = d.
- Suppose translation by G (τ_G) is induced by a projective linear map. Then τ_G^*L ≅ L.
- Pulling back L along τ_G sends a divisor D of degree d to D − G. By Abel–Jacobi, that is linearly equivalent to D if and only if dG = O. So q divides d.
- Lift the action to H⁰(L) and rescale so that M^q = I. A unique q-th root of the scalar exists because q ∤ p − 1, which follows from Hasse for p ≥ 7.
- If M restricted to V has only the eigenvalue 1, then M is the identity on V, because X^q − 1 is separable. So φ is constant on cosets of the order-q group ⟨G⟩. It sends every rational point of that group to one image and reveals nothing about k.
- Otherwise V contains an eigenvalue ζ ≠ 1, whose Galois orbit has size k′ = ord_q(p).
- So dim V ≥ k′. Over F_{p^r}, the total F_p-dimension is still at least k′.
- If k′ is small, MOV and Frey–Rück already apply.

**Further reason it fails.** Even in the multiplicative group, homogeneity only makes single translates cheap. Batched detection over an n×n grid becomes zero-entry detection in V_s·diag(φ)·V_bᵀ, with V_s and V_b Vandermonde matrices, which still costs about n². So the hoped gain was at most logarithmic even before the theorem.

**Consequence for this lens.**
- An exactly translation-invariant algebraic feature space that sees k must have dimension at least k′.
- An exact complex-valued invariant space of dimension D yields characters, and so the discrete log, in poly(D) evaluations.
- Approximate invariance is the existing Fejér/C1 signal question.
- Not covered: cheap nonlinear substitutions or correspondences. The degree-2 x-line correspondence is exactly the resultant, already costed in H019.

**Sources.** Elementary Abel–Jacobi argument as above. Mumford's theta-group theory is the background, from memory and not re-read. This is consistent with H013's Couveignes–Lercier dimension-q construction.

**Falsifier.** Already decided on paper. The root can check the proof in a few lines.

---

## Card 4 (killed by counting): Weil restriction through the F_{p²} trace

**Positive structure.** The trace map Tr(R) = R + π(R) on E(F_{p²}) is a cheap homomorphism onto E(F_p):
- It is surjective, because Tr restricted to E(F_p) is doubling, which is bijective on an odd-order group.
- Its kernel is the twist part.

Take the factor base {R : x(R) ∈ c + w·F_p}. Weil restriction of S3 over F_{p²} then gives 2 equations in 2 unknowns over F_p. Each labelled R₀ yields a relation R₀ = Tr(R₁) + Tr(R₂) with constant probability, at polylog cost. This is a genuine source of dimension in a prime-field problem.

**Why it loses.**
- The factor-base logs number about p, so it needs about p relations plus linear algebra: at least p work.
- Restricting the parameter t to a set of size m gives success m²/p per attempt. Total p/m + m² is minimized at about p^{2/3}.
- Both exceed √q. This is the n=2 case of Gaudry 2009 and Diem (memory), and it overlaps H012-PC4's F_{p²} lifts.

**Verdict.** Rejected by exact counting.

---

## Seeds rejected before cards (one-line reasons, scoped)

- **Cross-twist transport through the commuting x-only maps φ_k.** Ill-posed: φ_k depends on the integer k, and x(Q) fixes only k mod q. Transport needs a cross-group Diffie–Hellman primitive.
- **Anomalous-companion or amicable-pair transfer.** Needs a global lift of Q, which is the xedni or height wall.
- **CM/Deuring complex uniformization.** Constructing the Hilbert class polynomial already costs about √p before any torsion work.
- **Dual-number (tangent) Smart analogue.** Lifting the target consistently requires knowing k.
- **Endomorphisms through smooth ideal chains.** They act as scalars, which already cost polylog.
- **Separable identity x(U+V) − x(U−V) = −4·y_U·y_V/(x_U − x_V)².** Elementary. Its quadratic-character form is exactly the H003 collapse.
- **Full-group convolutions Σ_P F(P)·G(P+D).** This is a pushforward along 1 − π, so it is a low-degree function of D with no log information.
- **Translation-window Koopman/DMD on known feature families.** Bounded by the surviving A2 and bit-L1 lemmas, or a duplicate of Fejér C1.

## Recommendation for the root

1. Verify R1 (Card 1). If accepted, mark the SP3 and H019 three-list detectors as conditionally 3SUM-hard for random lists, and record the scope exclusions above.
2. Record R2 (Card 3) as an exact scope theorem for translation-linear representations.
3. Correct H001's Wagner statement to the translation-searchable filter requirement in Card 2.

No experiment is justified. Improvement remains **NONE**.
