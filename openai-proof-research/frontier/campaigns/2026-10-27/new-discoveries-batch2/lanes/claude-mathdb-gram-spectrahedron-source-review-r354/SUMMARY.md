# r354 — MathDB 404067 source qualification and audit of the r349 route

Lane: `claude-mathdb-gram-spectrahedron-source-review-r354` (Claude Opus 5.5, review sub-agent).
Single hypothesis: MathDB 404067 ("generic singleton Gram spectrahedra for sums of squares of quadratics").

**Disposition: PARK. No credit-eligible result. Counts unchanged: 9 additional / 39 total / next 40.**

The source is now qualified (the actual question was read and the standard reading confirmed). r349's T1 is
**refuted** by an exact counterexample, and the T2 proof mechanism is refuted too. A corrected route gives only
an upper bound m(n) ≤ m\*(n): unconditional for 2 ≤ n ≤ 8 (by exact computation) and conditional on a
Fröberg-type degree-4 statement for larger n. It is a routine adaptation of Blomenhofer's own duality
framework. No route to the matching lower bound survives, and a bounded exact probe suggests that at n = 4 the
bound m\*(4) = 4 may not be reached. A full answer to the source question is not tractable here.

## 1. Inputs, freezing and access

* All inputs were hashed (sha256 + size) **before** their contents were read: `input-freeze.json`, 41 files.
  These are the r350 intake (excluding its nested r326/r348 historical copies, which were not used), the r349
  originals, and `helper_guard.py`. They are referenced in place; nothing was copied.
* Bindings: every r349 original matches its r350 frozen copy byte for byte, and every r350 manifest entry
  matches the freeze. After the work all 41 inputs were re-hashed and still match (`checks/verify.py` repeats
  this check).
* MathDB: **zero requests** (429 HOLD). No Google, GitHub, ScienceDirect, browser or account activity.
* Network: three public GET requests, no errors or challenges (see `provenance.json`):
  1. MFO open-access OWR 2023/14 PDF (`publications.mfo.de`, handle mfo/4030).
  2. arXiv PDF 1512.04324 (Nenashev).
  3. arXiv abstract page 2305.06860 (version check: v1 only).

## 2. Source qualification (actual primary bodies read)

**OWR 2023/14, "Real Algebraic Geometry with a View toward Koopman Operator Methods"**: talk abstract
*A Semidefinite Algorithm for Powers-of-Forms Decomposition* by Alexander Taveira Blomenhofer, journal
pp. 791–792. MathDB's "page 52" is PDF page 52, which is journal p. 792. Verbatim question (p. 792):

> What is the maximum number m(n) for which there exists a Euclidean open subset U of the space of m-tuples
> of quadratics in n variables such that for all q = (q1,…,qm) ∈ U, Σ qi² has a singleton Gram
> spectrahedron? So far, it is only known to me that n − 1 ≤ m(n) < C(n+1,2).

**Interpretation is resolved in favour of the standard Gram spectrahedron.** The same abstract writes
decompositions f2 = Σ_{i=1}^N p_i² with arbitrary quadratics p_i and the Gram tensor in Gram(f2). The
companion paper arXiv:2305.06860 (§2.1, eq. (2.8)) defines Gram(f) = {G ⪰ 0 : [X]_k^T G [X]_k = f} over
the full monomial vector. Its Question 4.11 is the same problem, stated as "uniquely Sum-of-Squares
representable" with linearly independent q_i. Singleton Gram spectrahedron is equivalent to unique SOS
representation up to orthogonal transformations (2305.06860 §4.1). r349's "q_i-relative" alternative reading
is moot.

**Closest proof bodies** (2305.06860, frozen r349 copy, sha256 9f2266ff…; read in full in the relevant
sections):

* Lemma 4.7 and Corollary 4.8 (real-variety argument for m ≤ n − 1). This is the source of the lower bound.
* Proposition 4.4: under m ≤ rank°_k(n,2k), uniqueness is equivalent to sosupp f2 = ⟨q⟩.
* Appendix B: the primal/dual SDP pair, moment matrices M_E, strict complementarity and "dual nondegenerate
  SOS support".
* §4.2, Conjectures 4.10 and 4.12: numerical evidence for uniqueness at m = n + r for large n, and for an
  explicit family of ⌈(n+2)(n+1)/6⌉ quadratics in 2n variables.

The paper contains no theorem on m(n) beyond n − 1 ≤ m(n). The dual-certificate machinery used in §4 below
is already in Appendix B.

## 3. Audit of r349 T1/T2 (exact)

Notation: v is the monomial vector of quadratics (length N = C(n+1,2)). mult(G) = vᵀGv. G0 = AᵀA. U is the
span of the q_i, W = ker G0 = U^⊥, and κ = dim ker(mult).

**Lemma A (feasible directions; ordinary proof).** Let G0 ⪰ 0 with W = ker G0. A symmetric K satisfies
G0 + tK ⪰ 0 for some t > 0 **iff** K|_W ⪰ 0 and every w ∈ W with wᵀKw = 0 has Kw = 0.

*Proof.* Use a basis adapted to W^⊥ ⊕ W. Then G0 = diag(P, 0) with P ≻ 0, and K = [[A, B], [Bᵀ, C]]. For
small t, P + tA ≻ 0. By the Schur complement, G0 + tK ⪰ 0 iff C ⪰ t·Bᵀ(P+tA)⁻¹B.

* (⇒) This forces C ⪰ 0. For w ∈ ker C it gives 0 ≥ t·|(P+tA)^{-1/2}Bw|², so Bw = 0 and hence Kw = 0.
* (⇐) Write W = ker C ⊕ ran C. Since Bw = 0 on ker C, the form Bᵀ(P+tA)⁻¹B is supported on ran C. There
  C ≻ 0 dominates it for small t. ∎

Gram(f_q) = (G0 + ker mult) ∩ PSD is convex. So it is a singleton iff ker(mult) contains no nonzero direction
satisfying Lemma A. This depends only on W, hence only on U (r349's remark on this point is correct). The
direction "every nonzero K ∈ ker(mult) is indefinite on W ⇒ singleton" is correct. **The converse fails.**

**Counterexample to T1 (exact; `checks/check_t1_t2_counterexamples.py`).** Take n = 2, q = (x²), f = x⁴.

* ker(mult) = ℝ·K0, where K0 = E13 + E31 − 2E22.
* W = span(xy, y²), and K0|_W = diag(−2, 0): nonzero, semidefinite, not indefinite. T1 therefore predicts
  "not singleton".
* But in G0 + tK0, the principal minor on {x², y²} equals −t², so Gram(x⁴) = {diag(1,0,0)} is a singleton.
* With K = −K0 this also refutes the T1 proof step "K|_W ⪰ 0 ⇒ G0 + tK ⪰ 0 for small t". The off-diagonal
  block is incompatible with the singular restriction, exactly as root suspected.

**Counterexample to the T2 mechanism.** Take n = 2, m = 2, q = (xy, y²), f = x²y² + y⁴. Then w = 1 and
w(w+1)/2 = 1 = κ. Here K0|_W = 0 (so ker mult ∩ L_W ≠ 0), and the same minor equals −t², so Gram(f) is a
singleton. T2's step "K|_W = 0 ⇒ not singleton" is false. The pointwise statement "w(w+1)/2 ≤ κ ⇒ no m-tuple
has a singleton spectrahedron" is false as well. The generic conclusion m(2) = 1 is unaffected.

## 4. Corrected route: what survives

**Lemma C (ordinary proof).** Let n ≥ 2. If Gram(f_q) is a singleton, then (q)_4 ≠ S_4, where (q)_4 is the
degree-4 part of the ideal (q_1, …, q_m).

*Proof.* If f is in the interior of the closed cone Σ_4, then f − ε·vᵀv ∈ Σ_4 for some ε > 0, so f has a
PD Gram matrix H + εI. If G0 is PD, then G0 + tK0' ≻ 0 for small t and any nonzero K0' ∈ ker mult (κ ≥ 1
for n ≥ 2). Either way the spectrahedron is not a singleton. So f ∈ ∂Σ_4, and there is a nonzero E ∈ Σ_4\*
(equivalently M_E ⪰ 0) with E(f) = 0. Then Σ E(q_i²) = 0 with each term ≥ 0. Cauchy–Schwarz for M_E gives
E(q_i g) = 0 for all quadratics g, so 0 ≠ E ⊥ (q)_4. ∎

**Corollary C′.** Suppose some m0-tuple of real quadratics in n variables satisfies (q)_4 = S_4. Then
m(n) ≤ m0 − 1.

*Proof.* For m ≥ m0, the set {q : (q)_4 = S_4} is nonempty (append quadratics to the m0-tuple) and Zariski
open (a maximal minor is nonzero), hence Euclidean-dense. Every Euclidean-open set of m-tuples therefore
contains a non-singleton tuple. ∎

Koszul syzygies give dim (q)_4 ≤ mN − C(m,2), so (q)_4 = S_4 requires mN − C(m,2) ≥ C(n+3,4). Define

  **m\*(n) := max{m : mN − C(m,2) < C(n+3,4)}**.

This reproduces r349's T2 numbers exactly for n = 2..10 (1, 2, 4, 5, 6, 8, 10, 12, 14), asymptotically
m\*(n) ≈ (1/2 − 1/√6)·n². r349's conclusion matches the right threshold, but its proof was wrong.

`checks/check_degree4_generation.py` gives exact certificates: rank over F_p ≤ rank over ℚ, and the Koszul
bound is an upper bound. For n = 2..8 an explicit integer (m\*+1)-tuple has (q)_4 = S_4, and an m\*-tuple
attains the Koszul value. Hence:

* **Unconditionally for 2 ≤ n ≤ 8: m(n) ≤ m\*(n).** Values: 1, 2, 4, 5, 6, 8, 10, versus the source bound
  m(n) ≤ C(n+1,2) − 1.
* For general n this needs "generic (m\*+1) quadrics fill S_4": Fröberg's conjecture in degree 4, i.e.
  non-defectivity of the secant varieties of squares of quadrics in the filling range. Nenashev
  (arXiv:1512.04324, Theorem 1, read) only gives filling for z ≥ C(n+3,4)/N + N ≈ 0.58n², far above m\* ≈ 0.092n².
  No general reference was found in the bounded search.

**Lemma D (sufficient dual certificate; essentially 2305.06860 App. B and Prop. 4.4).** Suppose:

* E ⊥ (q)_4 with M_E ⪰ 0 and ker M_E = U, and
* the products q_i q_j (i ≤ j) are linearly independent.

Then Gram(f_q) is a singleton. *Proof:* every PSD Gram matrix G satisfies ⟨M_E, G⟩ = E(f) = 0, so
im G ⊆ U and G = AᵀSA with Σ S_ij q_i q_j = Σ q_i². Independence of the products forces S = I. ∎

The condition is open near any q0 where dim (q)_4 is locally constant: project E0 onto (q)_4^⊥. The rank of
the moment matrix is lower semicontinuous and bounded above by N − m, so the kernel stays exactly U(q), and the
nonzero eigenvalues stay positive.

**Proposition E (n = m = 4, exact reduction).** Let q be a regular sequence of 4 quaternary quadrics (a
Zariski-open dense condition). Then A = S/(q) has Hilbert series (1+t)⁴, so (q)_4^⊥ = ℝE is spanned by the
socle functional, and M_E induces the Poincaré-duality pairing A_2 × A_2 → A_4 ≅ ℝ. That pairing is
nondegenerate (Gorenstein), so rank M_E = 6. Hence:

  **Gram(f_q) is a singleton ⇔ the pairing on A_2 (dim 6) is definite.**

* (⇐) Lemma D, with the products independent because q is a regular sequence.
* (⇒) Lemma C's E is ±E (since (q)_4^⊥ = ℝE).

This condition is open. So **m(4) = 4 iff some real regular 4-tuple has a definite A_2 pairing, and otherwise
m(4) = 3.**

*Bounded exploratory probe (no proof, no credit).* `checks/probe_n4_m4_*.py` computes the exact inertia (exact
characteristic polynomial + Descartes, valid since the matrix is symmetric):

* 1060 random integer 4-tuples: signatures only 0, ±2, ±4.
* 120 perturbations of structured seeds — the complex squaring map (z1², z2²), the quaternion square and
  (z1z2, z1² − z2²): signatures only ±2, ±4.
* **No definite (±6) instance was found.**

An unverified remark, not relied on: by the Eisenbud–Levine–Khimshiashvili theorem this signature should be
the topological degree of q : ℝ⁴ → ℝ⁴, so m(4) = 4 would need a quadratic map of degree ±6. If no such map
exists, then m(4) = 3 < m\*(4), and m\*(n) is **not** the answer in general.

## 5. Why no full-scope answer (exact obstruction)

The source asks for m(n) for all n.

* **Upper side.** Survives only as m(n) ≤ m\*(n): unconditional for n ≤ 8, conditional (Fröberg degree 4)
  beyond. It is a routine consequence of SDP duality and of Blomenhofer's own framework (his Prop. 4.4
  hypothesis m ≤ rank°), so it is not credit-eligible as a new result.
* **Lower side.** The only proven mechanism (Lemma 4.7: real points of V(q) spanning W) needs V_ℝ(q) ≠ ∅,
  which fails generically once m ≥ n. Beyond that one needs, for every n, open families of strictly
  complementary PSD functionals E ⊥ (q)_4 that are not moment functionals of measures. No construction is
  known to me. The first nontrivial case (n = 4) already reduces to an unresolved definiteness/degree
  question, and the bounded evidence there leans against m\* being attained.
* Blomenhofer's numerics (Conj. 4.10, 4.12) suggest m(n) − n → ∞ for large n, but they do not pin down the
  threshold.

Hence there is no tractable full-scope proof or counterexample. Per the brief, the target is parked without
speculative proof.

## 6. Credit assessment

| Item | Status | Credit |
|---|---|---|
| Source reading (standard Gram spectrahedron, verbatim question) | verified, primary body | none (qualification) |
| T1 refutation; T2-mechanism refutation | exact counterexamples | none (audit of our own proposal) |
| Lemma A, C, C′, D | ordinary proofs above | none (standard SDP duality / routine adaptation of 2305.06860 App. B) |
| m(n) ≤ m\*(n) for n ≤ 8 | exact mod-p certificates | none (instances; bound, not answer) |
| Prop. E reduction for n = 4 | ordinary proof | none (instance reduction; undecided) |

## 7. Completed scope and remaining obligations

**Completed:**

* Froze and validated the inputs.
* Read the actual OWR question and the closest proof bodies (2305.06860 §§2, 4, App. B, App. C) and Nenashev
  Theorem 1.
* Reconciled the quantifiers: standard reading; Euclidean-open set of m-tuples, all with singleton Gram(Σ q_i²).
* Refuted T1 and the T2 mechanism exactly.
* Gave the corrected feasible-direction criterion and a corrected upper bound (unconditional for n ≤ 8).
* Reduced n = 4 to a definiteness question, with a bounded negative probe.

**Remaining** (not done; none claimed):

* (i) Decide m(4): either prove every real regular quaternary 4-tuple has an indefinite A_2 pairing, or find a
  definite one (exact).
* (ii) A general-n Fröberg degree-4 filling statement for (m\*+1) quadrics, or a reference for it.
* (iii) Any general lower-bound construction for n ≤ m ≤ m\*(n).
* (iv) Full current prior-art clearance. The search here was bounded: 3 web searches plus the arXiv version
  check. The Zenodo/GitHub experiment data for 2305.06860 was not inspected (GitHub is barred; Zenodo was not
  accessed). Nothing in this lane claims novelty.
