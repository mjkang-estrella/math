# Claude focused solving lane: projection constant < 4/3 versus distance to the cube

Disposition: **UNRESOLVED. Zero nominations.** No PROOF.md, no Lean, no manuscript. Root alone
accepts/counts/stages; counts 9 additional / 39 total, next 40, are unchanged and were not touched.

## 0. Literal target (read from the frozen primary body)

Deregowska–Lewandowska, *Projection Constants and Banach–Mazur Distance in Codimension Two*,
arXiv:2610.06141v1 (5 Oct 2026, only version per r215 history), **Conjecture 1.1, p.3**: for every N
and every nonzero real subspace V of l_inf^N, n = dim V, with lambda(V) < 4/3,

    d(V, l_inf^n) <= lambda(V) / (4 - 3 lambda(V)).

All real parameters, all n, N and the strict threshold are retained. The body was read from my frozen
copy `inputs/r215/frozen/projection.pdf` (sha256 471cb260…, identical to r215's freeze), extracted to
`extract/projection.txt`. Read in full: §1 (definitions, (1)–(4), Conjecture 1.1, the remark on
equivalence with all finite-dimensional spaces), §2 (Thm 2.1, Lemmas 2.1–2.4, Thms 2.2–2.4), §3
(condition (11), Props 3.1–3.4), references. The closest proof body (Deregowska–Foucart–Lewandowska,
arXiv:2509.16807v1, Theorem 1, Lemmas 2/3) was re-read from my frozen copy `inputs/r215/frozen/closest.pdf`.

**Correction to the inherited record (page 3):** the garbled range of the quantitative Zippin/Bernau
estimate is **0 < eps < 17^(-8)**. The pdftotext bounding boxes put the token "−8" at a raised baseline
(yMax 461.2 vs 468.4) immediately after "17" (`extract/p3-bbox.html`). The source contrasts this
tiny range with its own eps < 1/3. That quantitative statement is quoted by the source from
Godefroy–Kalton–Lancien (GAFA 10 (2000) p.809), a body I did not retrieve (gap, §7).

## 1. Independent assessment of inherited r215 deductions (used only after checking)

* **Conditional bridge (11) ⇒ distance.** Re-derived; correct (it is the source's own §3 remark).
* **Row-weighted inequality** ||H_l||_1 <= 1 + Σ_i δ_i |(Z^{-1})_{li}|: re-derived line by line.
  Row i in S of P gives ||(ZH)_i||_1 <= δ_i + |Z_ii| − Σ_{j≠i}|Z_ij|. The columnwise reverse triangle
  inequality gives Σ_i |c_i|(|Z_ii| − Σ_{j≠i}|Z_ij|) <= ||c^T Z||_1, then take c^T = e_l^T Z^{-1}.
  This is correct, and negative δ_i are allowed as written.
* **Signed rank-one falsifier** (N=20, f = ten 21/200 and ten −1/200): f·u = 1, ||f||_1 = 11/10,
  L = 11/10. Correct as a falsifier of the all-projections weighted shortcut only.
* **Symmetric cut cubes** max(||x||_inf, (a/n)||x||_1), n>=3, 1<a<4/3: rechecked the equivariant form
  F(y,z) = αy + βΣ_s s z_s and the sign-row norm a|α| + c_n|1−α|. Also rechecked c_3 = 3/2 and
  c_{n+1} >= c_n (conditional Jensen). λ = d = a is correct. Not repeated as an outcome.

## 2. New rigorous bridge A: fractional allocation suffices (weaker than (11))

**Theorem A.** Let P be a real idempotent N×N matrix of rank n with ||P||_inf = 1+eps, eps < 1/3,
and range V. Suppose there are distinct k_1..k_n in [N] and weights w_ij >= 0 with
Σ_i w_ij <= 1 for every j and Σ_j |p_{k_i j}| w_ij >= 1−eps for every i. Then
d(V, l_inf^n) <= (1+eps)/(1−3eps). Applied to a minimal P this gives Conjecture 1.1 for V.

*Proof.* Put y_i = Σ_j sgn(p_{k_i j}) w_ij e_j and x_i = P y_i ∈ V. Then (x_i)_{k_i} =
Σ_j |p_{k_i j}| w_ij >= 1−eps, and for every row l we have Σ_i |(x_i)_l| <= Σ_j |p_lj| Σ_i w_ij <= 1+eps.
Define T a = Σ a_i x_i. Then ||T a|| <= (1+eps)||a||. If |a_m| = ||a||_inf, row k_m gives
Σ_{i≠m} |(x_i)_{k_m}| <= (1+eps) − (1−eps) = 2eps. Hence |(Ta)_{k_m}| >= |a_m|(1−eps−2eps) =
(1−3eps)||a||. So T is an isomorphism with ||T|| ||T^{-1}|| <= (1+eps)/(1−3eps). Minimal
projections exist by compactness. ∎

Integral packings (11) are the case w ∈ {0,1}. **LP duality** (for fixed agents K): such w exists iff
for every probability vector μ on K, Σ_j max_{k∈K} μ_k |p_kj| >= 1−eps. This is exactly the hypothesis
shape in Dor's lemma that Bourgain 1982 invokes (§7). The passage from max-conditions to (near-)
disjoint sets is classical, and this bridge is a routine LP relaxation. **No novelty is claimed.**

**Theorem A′ (V-intrinsic corollary).** Suppose there are distinct k_1..k_n and x^(i) ∈ V with
||x^(i)||_inf = 1 = x^(i)_{k_i} and Σ_i (2|x^(i)_j| − 1)_+ <= 1 for every j. Then every projection onto V
with norm 1+eps < 4/3 satisfies Theorem A's hypothesis, so d <= λ/(4−3λ).
*Proof.* Take w_ij = (2|x^(i)_j|−1)_+. Then Σ_j |p_{k_i j}| w_ij >= Σ_j |p_{k_i j}|(2|x^(i)_j|−1)
>= 2|Σ_j p_{k_i j} x^(i)_j| − Σ_j |p_{k_i j}| >= 2 − (1+eps). ∎
The source's geometric property (disjoint sets outside which |v| <= 1/2) is the special case where
the supports of the summands are disjoint. **Exact check** (`tools/exp5_geofrac_w.py`, rational
arithmetic) on the source's Prop 3.2 space V = span(u,v) ⊂ R^5, where the integral property provably
fails: x = u (peak at coordinate 1) and y = (44/287, 1004/1435, 1, 265/287, 652/1435) (peak at
coordinate 3) give max_j penalty exactly 1. Padding by e_6 and the repeated pairs yields A′ for every
W_n, n >= 3. So A′ strictly extends the source's geometric mechanism. It recovers only an
already-public case (source Prop 3.3/3.4 give the W_n conclusion) and is not a new outcome. Whether A′
holds for all V with λ(V) < 4/3 is open here. It does not involve λ at all, so presumably it fails
near λ = 4/3.

## 3. New rigorous family result B: first-order rigidity near the cube (excludes a mechanism)

Let U be an m×n real matrix with rows u_j, ||u_j||_1 = 1, **no u_j equal to ±e_i**. Fix real c_j with
c* = max_j c_j > 0. For η>0 let V_η = {(x, F_η x)} ⊂ l_inf^{n+m}, F_η rows (1+ηc_j)u_j.

**Theorem B.** λ(V_η) = 1 + ηc* + O(η²) and d(V_η, l_inf^n) = 1 + ηc* + O(η²). Hence d − λ = O(η²), while
λ/(4−3λ) − λ >= 3ηc*(1+O(η)), so Conjecture 1.1 holds for all small η in every such family. This is a
family/parameter result: no credit.

*Proof.* The identity map gives d <= max(1, max_j ||φ_j||_1) = 1+ηc*. Also λ <= d. Every projection onto
V_η has the form P(y,z) = (Ay+Bz, F(Ay+Bz)) with A = I − BF, since x-coordinates determine elements of V_η.
The row-i norm of the cube rows is |1−t| + Σ_{l≠i}|v_l| + ||B_i||_1 with v = B_iF, t = v_i. This is
>= 1 + h_0(B_i) − 2η·max_j|c_j|·||B_i||_1 (since ||bF_η − bU||_1 <= η·max_j|c_j|·||b||_1), where h_0(b) = ||b||_1 − |(bU)_i| + Σ_{l≠i}|(bU)_l| >= ||b||_1 − ||bU||_1 >= 0.
h_0 is continuous and positively homogeneous. If h_0(b) = 0, then bU has no cancellation and is
supported on {i}, so every u_j in supp b is ±e_i, which is excluded. Hence h_0(b) >= κ||b||_1 for some
κ = κ(U) > 0. A projection of norm <= 1+ηM therefore has max_i||B_i||_1 <= ηM/(κ − 2η max|c|) = O(η) for small η.
Row j of the cuts is ||φ_j − φ_jBF||_1 + ||φ_jB||_1 >= ||φ_j||_1 − ηc*||φ_jB||_1, because ||wF||_1 <=
(1+ηc*)||w||_1. Since ||φ_jB||_1 = O(η), this is 1 + ηc_j − O(η²). Maximize over j. ∎

Consequence: first-order (small-eps) counterexamples cannot come from non-degenerate cut
perturbations of the cube. Any small-eps counterexample must involve clustered coordinate
functionals (u_j = ±e_i, i.e. several vertices of the dual ball near one cross-polytope vertex). The
W_n spaces and averaging projections are of exactly this type.

## 4. Routes attempted toward a universal proof, and where each stops

1. **Fractional packing for an arbitrary idempotent** (Theorem A's hypothesis for every P, ||P|| < 4/3).
   No proof. The LP dual reduces it to: for every μ, Σ_j max_k μ_k|p_kj| >= 1−eps. Lower-bounding the
   max needs test vectors y_k with Σ|y_k| <= 1 and Σ μ_k (P y_k)_k >= 1−eps. V-vectors give exactly A′
   (P-independent), and every non-V choice I tried reproduces the primal problem.
2. **Explicit allocations.** (a) self-referential w_kj = |p_jk| / Σ_{k'∈K}|p_jk'|, motivated by
   Σ_j p_kj p_jk = p_kk; (b) w_kj = |B_jk| / max(1, ||B_j||_1) with Auerbach-normalized basis. Both are
   **numerically falsified** as universal rules (adversarial loss coefficients c ≈ 37 and c ≈ 1.07 > 1;
   float leads, not exact certificates). Neither is a refutation of anything in the source.
3. **Extreme-point stability.** At eps = 0 there is a short elementary proof for polyhedral V: a vertex φ_k
   of the dual ball conv(±φ_j) forces row k of any norm-one projection to be supported on {j : φ_j = ±φ_k}.
   That yields n disjoint rows. For eps > 0 the representation mass can leave the vertex class unless the
   vertex is quantitatively exposed. The quantitative form needs peak vectors whose >1/2 parts are
   fractionally disjoint, which is A′ again. No universal exposedness bound is available.
4. **Contraction induction** on a coordinate with p_kk >= 1−eps. P' = P − (Pe_k/p_kk) ⊗ (row k) gives a
   projection of norm <= 1+eps onto {x∈V : x_k = 0} restricted to [N]∖{k} (proved for eps <= 1/3). The
   distance, however, accumulates a multiplicative loss per step, so the bound becomes dimension-dependent.
5. **Rank/trace (Lemma 2.1) route.** It only removes the N−2m large-diagonal singletons. The residual
   problem is a dim d <= m subspace of R^{d+m}, which is not smaller in kind.

## 5. Exploratory numerics (float, lp_solve; support only, never proof)

All runs are guarded and logged under runs/ (exact commands in RUN.md):

| run | object | result |
|---|---|---|
| exp1, exp2a–c | 2-dim V, N=5..7 (codim >= 3, outside the source), adversarial climbs | sanity: hexagon λ=4/3, d=3/2. Heavy re-evaluated optima have d ≈ λ: ρ = (d−1)/(bound−1) ≈ 0.23–0.25. No violation lead |
| exp3 (c) | loss coefficient c = (1−t*)/(‖P‖−1) of the best fractional allocation, ‖P‖ ∈ [1.01, 4/3) | max c: 0.69 (n=2,N=5, minimal P); 0.55 (n=3,N=6, minimal P); 0.31/0.14 (arbitrary conjugated idempotents). Fractional packing held in all runs; integral packing number = n at all reported optima |
| exp4 | Auerbach (max-volume) agents R, LP allocation | max c 0.69 (n=2,N=5,6), 0.66 (n=3,N=6, minimal), 0.28/0.15 (n=3, N=6/7, arbitrary). Never > 1 |
| exp4 | explicit allocations 'self', 'geo' | c ≈ 37 and ≈ 1.07: rules fail |
| exp5 | A′ on source V ⊂ R^5 | holds exactly (penalty 1) |

These are local searches in small dimensions. They cannot represent all idempotents and are not
evidence of universality.

## 6. Exact missing lemma (strongest surviving route)

**Auerbach fractional packing (conjectural).** Let P be any real idempotent of rank n with
||P||_inf = 1+eps < 4/3, and let R be n coordinates maximizing |det B_R| for a basis matrix B of
range P. Then for every probability vector μ on R, Σ_j max_{k∈R} μ_k |p_kj| >= 1−eps.
By LP duality and Theorem A this implies Conjecture 1.1. It is stronger than the conjecture, and a
counterexample to it would **not** refute the source. Numerically the worst observed loss coefficient
is ≈ 0.69 < 1, suggesting slack of order 0.3·eps. Even the weaker unselected version (some K works) is
unproved. Obstruction: the only identities linking the agent rows A = P_{R,:} to the norm constraint are
AB = I and ||(BA)_l||_1 <= 1+eps. Coordinates with ||B_l||_1 > 1 force cancellation between agent rows,
and I could not convert that cancellation into the μ-weighted max lower bound.

## 7. Prior art and subsumption (bounded)

* **Bourgain, "A remark on finite-dimensional P_λ-spaces", Studia Math. 72 (1982) 285–289,
  DOI 10.4064/sm-72-3-285-289.** Retrieved 2026-10-30T07:28Z from the publisher's free CC-BY route
  (IMPAN page, redirected to matwbn.icm.edu.pl/ksiazki/sm/sm72/sm72120.pdf), frozen (sha256 0c097b3e…)
  and read from rendered pages 1 and 3. Theorem 1 gives a subspace F with dim F > c_λ^{-1} dim E and
  Δ(F, l_inf^m) <= c_λ. Proportional subspaces only; it states the full-dimension question as open. It
  neither subsumes nor refutes Conjecture 1.1. Its last step uses Dor's lemma (Ann. Math. 102 (1975),
  Prop 2.2) under a max-condition of the Theorem A dual form, so the fractional bridge is classical in spirit.
* Zippin 1981/1984, Dor 1975, GKL 2000 and Bernau: **not retrieved**. The source itself says the known
  quantitative general estimate covers only eps < 17^(-8), but a sharper older result is not excluded by
  me. No GitHub/ScienceDirect/Google-challenge or other denied route was attempted, and no retries,
  proxies or bypasses were used. No live public proof-registry head was checked in this lane, so the
  current complete registry gap remains.
* No novelty or priority is asserted for Theorems A, A′ or B. Each is short, and B is a parameter-family result.

## 8. Bottom line

No proof and no counterexample of Conjecture 1.1. Delivered: a strictly weaker sufficient condition
(Theorem A) with an LP-dual characterization; a λ-free geometric criterion (A′) that covers the source's
obstruction spaces; a rigorous first-order rigidity theorem (B) that rules out non-degenerate
small-eps counterexamples; two falsified explicit-allocation shortcuts; and a precise surviving
missing lemma (§6) with numerical slack. Strongest objection: everything universal here is a
reduction or a family result. The open core is the fractional packing statement for arbitrary
idempotents, and the routes in §4 all stop at the same μ-weighted max lower bound.
