# Solid k-minors are k-essential

*A proof of Conjecture 4.6 of Brosowsky, Chepuri and Mason, with a Lean 4 formalization.*

MathDB 337947. The proof is from a GPT-6.1 Sol lane (`t1-pool077-proof-sol61-20261120-r1`). The adversarial review is by Claude Opus 5.5 (`t1-prelean-X41-opus-20261120-r1`). This manuscript and the Lean formalization are by Claude Opus 5.5 (`k-essential-minors-337947-formal-paper-opus55-20261120-r1`, 2026-11-20). The final pre-publication check is also by Claude Opus 5.5 (`t1-final-check-337947-opus55-20261120-r1`), so it is not independent of the packager's model family. The Lean development has 6 modules and 1,092 lines. It is checked by the Lean kernel, and its final theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. The source is listed in the appendix [LEAN-SOURCE-APPENDIX.md](LEAN-SOURCE-APPENDIX.md).

## 1. The conjecture and the source's definitions

Source: A. Brosowsky, S. Chepuri, A. Mason, *Parametrizations of k-Nonnegative Matrices: Cluster Algebras and k-Positivity Tests*, arXiv:1712.05037 (v3, January 2021), Section 4. The journal version is J. Combin. Theory Ser. A 174 (2020) 105217; we did not read the publisher's text. The conjecture is numbered 3.11 in v1 and 4.5 in v2. It first appears as the first part of Conjecture 4.2 in the 2017 University of Minnesota REU report of Brosowsky, Kulkarni, Mason, Suk and Tang, whose Proposition 4.1 proves k ≤ 3 by ε-power constructions like those of the paper.

The source's definitions, quoted verbatim from arXiv v3 (§2 and §4; [n] = {1,…,n}, [i, j] = {i, i+1, …, j}):

> **Definition.** For an m × n matrix X and sets I ⊆ [m], J ⊆ [n], we will let X_{I,J} be the submatrix of X where we take rows indexed by I and columns indexed by J. If |I| = |J| = ℓ, the determinant of this submatrix is |X_{I,J}|, and we call this a minor of order ℓ or more simply an ℓ-minor.

> **Definition.** A solid minor is a minor with rows indexed by I = [i, i + ℓ − 1] and columns indexed by J = [j, j + ℓ − 1].

> **Definition.** A minor |X_{I,J}| is k-essential if |I| = |J| ≤ k and there exists a matrix M such that |M_{I,J}| ≤ 0, but ∀(I′, J′) ≠ (I, J), |I′| = |J′| ≤ k, we have M_{I′,J′} > 0.
>
> That is to say, a k-essential minor must appear in all k-positivity tests consisting only of minors.

> **Conjecture 4.6.** Solid k-minors are k-essential.

The source never names the field. Its matrices are n × n, and positivity of minors places them over ℝ; the Lean statement is over ℝ. (The matrix constructed below has rational entries when t is rational, so the result also holds over ℚ.) The source proves k = 2 and k = 3 (Propositions 4.2 and 4.3) and calls k = 1 trivial. It adds: "Unfortunately, the technique used in Propositions 4.2 and 4.3 fails in the general case. … This has made extrapolating to the general case rather difficult."

### The Lean statement (verbatim the endpoint fixed by the review)

```lean
/-- minor with row set I and column set J (sorted embeddings) -/
noncomputable def minor {n} (M : Matrix (Fin n) (Fin n) ℝ) (I J : Finset (Fin n))
    (h : I.card = J.card) : ℝ :=
  (M.submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h.symm)).det

def interval {n} (a ℓ : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a ≤ i.val ∧ i.val < a + ℓ)

def KEssential {n} (k : ℕ) (I J : Finset (Fin n)) (h : I.card = J.card) : Prop :=
  I.card ≤ k ∧ ∃ M : Matrix (Fin n) (Fin n) ℝ, minor M I J h ≤ 0 ∧
    ∀ (I' J' : Finset (Fin n)) (h' : I'.card = J'.card), I'.card ≤ k → (I', J') ≠ (I, J) →
      0 < minor M I' J' h'

theorem solid_minors_k_essential (n k a b : ℕ) (hk : 1 ≤ k) (ha : a + k ≤ n) (hb : b + k ≤ n) :
    ∃ h, KEssential (n := n) k (interval a k) (interval b k) h
```

How the Lean statement matches the source:

| Source | Lean |
|---|---|
| index sets I ⊆ [n] | `Finset (Fin n)`, 0-based; row r of the source is `Fin` value r − 1 |
| X_{I,J}, rows and columns in increasing order | `M.submatrix` along `orderEmbOfFin`, the increasing enumeration |
| \|X_{I,J}\| | Mathlib's `Matrix.det` of that square submatrix |
| solid: I = [i, i+k−1], J = [j, j+k−1] | `interval a k`, `interval b k`, which are {a, …, a+k−1} and {b, …, b+k−1} in `Fin n`. Every solid k-minor arises from some a, b with a + k ≤ n, b + k ≤ n |
| \|I\| = \|J\| ≤ k | `I.card ≤ k` together with the card-equality proof `h` |
| some matrix M with \|M_{I,J}\| ≤ 0 | `∃ M : Matrix (Fin n) (Fin n) ℝ, minor M I J h ≤ 0` |
| ∀ (I′,J′) ≠ (I,J), \|I′\| = \|J′\| ≤ k: M_{I′,J′} > 0 | `∀ I' J' h', I'.card ≤ k → (I',J') ≠ (I,J) → 0 < minor M I' J' h'` |

Notes on fidelity:
- The Lean statement also quantifies over the empty pair (I′, J′) = (∅, ∅). Its minor is the 0 × 0 determinant 1 > 0, so this adds nothing. The sanity lemma `KEss.minor_empty` proves it.
- The existential `∃ h` is the equality |interval a k| = |interval b k|, which holds by `KEss.card_interval`. The theorem is therefore not vacuous: it produces, for every admissible n, k, a, b, a real matrix with the required sign pattern.
- The theorem is proved uniformly in n, k, a, b. No case is checked by computation.

## 2. Theorem

**Theorem.** Let 1 ≤ k ≤ n, and let I = {a, …, a+k−1} and J = {b, …, b+k−1} be index intervals inside {0, …, n−1}. There is a real n × n matrix M such that:
- det M_{I,J} = 0;
- det M_{I′,J′} > 0 for every other pair (I′, J′) with |I′| = |J′| ≤ k.

In particular, every solid k-minor is k-essential (Conjecture 4.6).

Throughout, r = k − 1 ≥ 0, and the nodes of a row or column index i are the integers i themselves.

## 3. Divided differences

For a finite set S ⊂ ℤ and f : ℤ → ℝ put

  D_S(f) = Σ_{y∈S} f(y) / Π_{z∈S∖{y}} (y − z).                                        (2)

**(D1) Interpolation.** Let P_S(f) be the Lagrange interpolant of f on S, of degree < |S|. Then D_S(f) is the coefficient of x^{|S|−1} in P_S(f). If P is a real polynomial of degree < |S|, then D_S(P) is the coefficient of x^{|S|−1} in P. Both statements are Mathlib's `Lagrange.coeff_eq_sum`, applied to P_S(f) and to P.

**(D2) Two-point recurrence.** For distinct i, j ∈ S,

  (i − j) · D_S(f) = D_{S∖{j}}(f) − D_{S∖{i}}(f).

*Proof.* The Neville–Aitken identity (Mathlib's `Lagrange.interpolate_eq_add_interpolate_erase`) gives

  P_S = P_{S∖{j}} · (x − j)/(i − j) + P_{S∖{i}} · (x − i)/(j − i).

Write |S| = N + 2 and compare the coefficients of x^{N+1}. The two smaller interpolants have degree ≤ N, so only their x^N coefficients contribute. With (D1) this gives D_S = D_{S∖{j}}/(i − j) + D_{S∖{i}}/(j − i). ∎

**(D3) Refinement.** Let x₀ < z < x_r, where x₀, x_r ∈ S and z ∉ S. Put Y = S ∪ {z}, L = Y ∖ {x_r} and R = Y ∖ {x₀}. Then

  (x_r − x₀) D_S(f) = (z − x₀) D_L(f) + (x_r − z) D_R(f).                                 (5)

*Proof.* Apply (D2) to Y twice: with (i, j) = (x_r, z) it gives (x_r − z) D_Y = D_S − D_L, and with (i, j) = (z, x₀) it gives (z − x₀) D_Y = D_R − D_S. Eliminate D_Y. ∎

**(D4) Generalized Vandermonde.** Let v₀, …, v_r be distinct integers and S = {v₀, …, v_r}. Then

  det [ v_s^0, v_s^1, …, v_s^{r−1}, f(v_s) ]_{s=0..r} = det [ v_s^d ]_{s,d=0..r} · D_S(f).        (9)

*Proof.* Let P = Σ_{e≤r} c_e x^e be the interpolant of f on S; by (D1), c_r = D_S(f). Define U as follows:
- its columns d < r are the unit vectors e_d;
- its last column is (c₀, …, c_r).

Then the left-hand matrix equals V·U, where V is the Vandermonde matrix: its last column is (P(v_s))_s = (f(v_s))_s. U is upper triangular with diagonal (1, …, 1, c_r). Therefore det(V·U) = det V · c_r. ∎

Finally, for strictly increasing real nodes, det V = Π_{s<s′}(v_{s′} − v_s) > 0 (Mathlib's `Matrix.det_vandermonde`).

## 4. The spline: exactly one zero divided difference (Lemma 1)

For a ∈ ℤ define U_a : ℤ → ℤ (this is r! times the function u_a of the proof under review):

  U_a(x) = Π_{h<r} (x − a − h)       if x < a,
  U_a(x) = 0                         if a ≤ x ≤ a + r,
  U_a(x) = Π_{h<r} (x − a − 1 − h)   if x > a + r.

U_a agrees with P₋(x) = Π_{h<r}(x − a − h) at every x < a + r, because P₋ vanishes at a, …, a+r−1. It agrees with P₊(x) = Π_{h<r}(x − a − 1 − h) at every x > a, because P₊ vanishes at a+1, …, a+r. Both are monic of degree r. For r = 0 the products are empty, and U_a(x) = [x ≠ a].

**Lemma 1.** For every S ⊂ ℤ with |S| = r + 1, D_S(U_a) ≥ 0, and D_S(U_a) > 0 unless S = [a, a + r].

*Proof.* We induct on the spread max S − min S. Let m = min S and M = max S.
- *Window case, S = [m, m + r].*
  - If m = a, U_a vanishes on S, so D_S(U_a) = 0. Here S is the exceptional set.
  - If m < a, every node is < a + r, so U_a = P₋ on S. By (D1), D_S(U_a) is the leading coefficient of P₋, which is 1.
  - If m > a, every node is > a, so U_a = P₊ on S, and D_S(U_a) = 1 likewise.
- *Other cases.* Then M > m + r, since otherwise S ⊆ [m, m+r] with |S| = r+1 would force S = [m, m+r]. So [m, M] contains an integer z ∉ S, and m < z < M. Apply (5) with x₀ = m and x_r = M:
  - L and R both have r + 1 elements, and spread at most M − m − 1.
  - By induction D_L, D_R ≥ 0, and the weights z − m and M − z in (5) are positive, so D_S ≥ 0.
  - Strictness: if m < a, then m ∈ L and m ∉ [a, a+r], so D_L > 0 by induction. If m ≥ a, then M > m + r ≥ a + r, and M ∈ R shows R ≠ [a, a+r], so D_R > 0.
  - Either way D_S > 0. ∎

## 5. The matrix and the lowest-order term of every minor (Lemma 2)

Index r + 2 features by d ∈ {0, …, r+1}, with weight w(d) = min(d, r): the weights are 0, 1, …, r−1, r, r. Define

| d | row feature F_d(i) | column feature G_d(j) |
|---|---|---|
| d < r | i^d | j^d |
| d = r | U_a(i) | j^r |
| d = r+1 | i^r | U_b(j) |

and, for t > 0,

  A(t)_{ij} = Σ_d t^{w(d)} F_d(i) G_d(j) = Σ_{d<r} t^d (ij)^d + t^r (U_a(i) j^r + i^r U_b(j)).        (6)

For k = 1 (r = 0) this is A_{ij} = [i ≠ a] + [j ≠ b], independent of t: 0 at the target entry and 1 or 2 elsewhere. (The source's k = 1 example instead puts −1 at the target and 1 elsewhere.)

**Function expansion.** Let P be an ℓ × m matrix and Q an m × ℓ matrix over a commutative ring. Expanding the Leibniz formula gives

  det(PQ) = Σ_{p : [ℓ]→[m]} (Π_s Q_{p(s), s}) · det(P_{·, p}).

Here P_{·,p} is the ℓ × ℓ matrix with columns p(1), …, p(ℓ). If p is not injective, two columns coincide and the term vanishes. If ι : [ℓ] → [m] is fixed, the terms with p = ι ∘ q (q : [ℓ] → [ℓ]) add up to det(P_{·,ι}) · det(Q_{ι,·}): this is the same expansion of the square product P_{·,ι} Q_{ι,·}. This replaces the subset form of the Cauchy–Binet formula.

Take row indices i₁ < … < i_ℓ and column indices j₁ < … < j_ℓ. Apply the expansion to P = (F_d(i_s)) and Q = diag(t^{w}) (G_d(j_s)):

  det A(t)[I, J] = Σ_p t^{W(p)} c_p,   W(p) = Σ_s w(p(s)),   c_p = (Π_s G_{p(s)}(j_s)) · det(F_{p(s′)}(i_s))_{s,s′}.

c_p = 0 unless p is injective. Put σ_ℓ = 0 + 1 + … + (ℓ−1).

**Weights.** Let p be injective and ℓ ≤ r + 1.
- (W1) W(p) ≥ σ_ℓ. Induct on ℓ: the largest value p(s₀) is at least ℓ − 1, and removing s₀ leaves an injection of ℓ − 1 points. The weight w is monotone.
- (W2) If ℓ ≤ r and W(p) ≤ σ_ℓ, then every p(s) < ℓ. By (W1) applied after removing s₀, w(p(s₀)) ≤ ℓ − 1 < r, so the largest value p(s₀) is ≤ ℓ − 1.
- (W3) Let ℓ = r + 1. Then p misses exactly one feature v, and W(p) = (σ_{r+1} + r) − w(v). So W(p) ≤ σ_{r+1} if and only if v ∈ {r, r+1}. Equivalently, p factors through one of the two order-preserving injections that skip r+1 or skip r.
- Conversely, if p = ι ∘ q with q a permutation and ι one of these injections (castLE for ℓ ≤ r), then W(p) = σ_ℓ, because w(ι(s)) = s.

**Lemma 2.** Let I, J have size ℓ ≤ k. Then c_p = 0 whenever W(p) < σ_ℓ, and Σ_{W(p) ≤ σ_ℓ} c_p equals:
- (ℓ ≤ r) V(I) V(J), where V(I) = det(i_s^d) = Π_{s<s′}(i_{s′} − i_s) > 0;
- (ℓ = k) V(I) V(J) · (D_I(U_a) + D_J(U_b)).

*Proof.*
- *Case ℓ ≤ r.* By (W2) the contributing p factor through the first ℓ features. The sum is det(i_s^d) · det(j_s^d) with d < ℓ.
- *Case ℓ = k.* By (W3) the contributing p factor through one of two injections, and no contributing p factors through both: it would then miss two features. The first injection uses features 0, …, r and gives det[1, …, i^{r−1}, U_a(i)] · V(J) = V(I) D_I(U_a) · V(J) by (9). The second uses features 0, …, r−1, r+1 and gives V(I) · V(J) D_J(U_b). ∎

**The target minor vanishes.** Let I = [a, a+r] and J = [b, b+r]. Then U_a = 0 on I and U_b = 0 on J. An injective p : [r+1] → [r+2] hits feature r or feature r+1:
- If it hits r, a column of (F_{p(s′)}(i_s)) is U_a(i_s) = 0.
- If it hits r+1, a factor G_{r+1}(j_s) = U_b(j_s) = 0.

Every c_p vanishes, so det A(t)[I,J] = 0 for all t.

**Every other minor is positive for small t.**
- *Leading coefficient.* Let (I′, J′) ≠ (I, J) with |I′| = |J′| = ℓ ≤ k. By Lemmas 1 and 2 the degree-σ_ℓ coefficient is positive.
  - If ℓ ≤ r, it is V(I′)V(J′) > 0.
  - If ℓ = k, both divided differences are ≥ 0, and at least one is > 0, because I′ ≠ [a,a+r] or J′ ≠ [b,b+r].
  - (ℓ = 0 is included: the empty minor is 1.)
- *Small t.* For t > 0, det A(t)[I′,J′] = t^{σ_ℓ} g(t), where g(t) = Σ_p t^{W(p)−σ_ℓ} c_p is a polynomial and g(0) is that coefficient. So the minor is positive for all t in some interval (0, ε).
- *One common t.* There are finitely many pairs (I′, J′), so one t > 0 works for all of them simultaneously.

M = A(t) proves the theorem. ∎

In place of the explicit bound t = 1/(H+1) of the proof under review, the Lean proof uses continuity and a finite intersection of neighbourhood filters (`Filter.eventually_all`). The matrix is the same.

## 6. Map from the proof to Lean

| Step | Lean declaration (module) |
|---|---|
| statement, card of intervals, empty minor | `minor`, `interval`, `KEssential`, `card_interval`, `minor_empty` (`KEStatement`) |
| function expansion; non-injective terms vanish; one injection | `det_mul_expand`, `det_submatrix_eq_zero_of_not_injective`, `sum_comp_eq_det_mul_det`, `det_mul_diag_mul` (`KEExpand`) |
| selecting minimal p | `sum_filter_eq_sum_comp`, `sum_filter_eq_sum_comp_two` (`KEExpand`) |
| (W1), (W2), (W3) | `sum_le_sum_of_injective`, `lt_of_sum_min_le`, `exists_image_eq_erase` (`KEExpand`); `sum_val_le_W`, `W_comp`, `wt_succAbove` (`KELeading`) |
| small t | `eventually_pos_of_leading` (`KEExpand`) |
| (2), (D1)–(D4), Vandermonde positivity | `dd`, `dd_eq_coeff`, `dd_poly`, `dd_recurrence`, `dd_refine`, `genVand`, `det_genVand`, `det_vandermonde_pos` (`KEDivDiff`) |
| U_a, windows, Lemma 1 | `spline`, `u`, `dd_spline_window`, `dd_spline_window_target`, `dd_spline_pos` (`KESpline`) |
| matrix (6), Lemma 2 | `rowF`, `colG`, `wt`, `mat`, `coef`, `det_submatrix_mat`, `leading_low`, `leading_top` (`KELeading`) |
| target minor, eventual positivity, bridge to `interval`, theorem | `target_det_zero`, `core_eventually_pos`, `eq_interval_of_image`, `minor_eventually_pos`, `solid_minors_k_essential` (`KEMain`) |

## 7. Significance

**What the result settles.** Conjecture 4.6 of Brosowsky–Chepuri–Mason was open in every arXiv version, including v3 (January 2021), which postdates the journal version. Only k ≤ 3 had been proved. The authors state that their 0/1-block technique cannot extend past k = 3. The theorem settles the conjecture for all n, all k ≤ n and all solid positions.

**What it implies.** By the source's own reading of k-essentiality, every solid k-minor must appear in every k-positivity test that consists only of minors. So each of the (n − k + 1)² solid k-minors belongs to every such test, including those of the source's minimal tests that consist only of minors. The source's other question, whether these minors must appear in every k-positivity test (tests that may use non-minors), is not addressed here.

**Methods.** The proof is elementary: Vandermonde determinants, divided differences, a determinant expansion, and a small-parameter argument. It runs to about two pages.

**How significant.** The conjecture comes from a 2017 REU project, later published in J. Combin. Theory Ser. A, and is not a well-known problem. The reviewer estimated a probability of 0.65 that a specialist would regard the solution as not routine. The tools are classical in total positivity: polynomial kernels Σ t^d x^d y^d whose small-t minors are products of Vandermonde determinants (as in Karlin's *Total Positivity*), the identity between generalized Vandermonde determinants and divided differences, and the positivity of divided differences of splines, of which U_a is a discrete analogue of the Curry–Schoenberg B-spline. What is new is the assembly:
- a discrete spline whose (r+1)-point divided differences vanish on exactly one window;
- the sum of two opposite rank-one perturbations, so that the leading coefficient is a sum rather than a product.

The construction is unrelated to the source's ε-power matrices built around a 0/1 central block.

The second point matters: in the reviewer's control computation a single perturbation fails, with 1,106 failing minors already at n ≤ 6. We regard the result as a modest, clean resolution of a small open problem; the formalization makes it kernel-checked. We do not claim that it bears on the broader classification of minimal k-positivity tests.

## 8. Prior art (from the review, `REVIEW-337947.md` §1 and §3)

**Literature checked by the review.**
- All three arXiv versions and the author-hosted copy state the conjecture as open.
- OpenAlex lists seven citing works:
  - Choudhury (two papers);
  - Chepuri–Sherman-Bennett (two papers);
  - Soskin–Vishwakarma;
  - Vishwakarma 2025;
  - Ahmad–Yang.

  The review searched their saved full texts for "essential". The hits concerned essential sets and essential edges, not k-essential minors. None resolves the conjecture.
- Registry checks found no match:
  - searches of the Omega issue and PR registry for "1712.05037", "k-essential solid minors" and "Brosowsky Chepuri Mason" were empty;
  - the Principia ID list and clone have no hit;
  - the campaign's own lane and claim records do not contain it.
- A web search found only the source, a 2018 JMM poster and the 2017 REU report. All of them state it as a conjecture.

**Routes the review rejected.**
- Positroid cells of Gr_{≥0}(n, 2n) give only the corner minors, which are already covered by the source's Remark 4.1.
- TP_k-completion results decide whether a completion exists, not whether exactly one prescribed minor can be nonpositive.
- The solid-minor positivity test of the source's reference [5] concerns sufficiency, not essentiality.

**Refresh at the final check (2026-11-20).** OpenAlex still lists the same seven citing works. The ReuF2F benchmark (github.com/cmu-l3/reuF2F, 244 problems) has no entry for this source. Searches of the Omega registry's issues and pull requests, of GitHub code, of the Principia, mio-qwq and openai/math clones, and two web searches found nothing that resolves the conjecture.

**Caveat.** The publisher's version of record was not read.

## 9. Verification record

[REPORT.md](REPORT.md) contains the compile and kernel-check receipts, the axiom output, the clean rebuild and the replay from this appendix in a fresh directory.
