# Discovery report — lane pi-matrix-discovery-r6 (pi, solo)

**Campaign:** 2026-10-26/new-discoveries
**Date:** 2026-10-26
**Verdict: NO NEW DISCOVERY CLAIMED.** One target (MathDB 371031, the Tang–Zhang
closed-form Schatten constant conjecture) was **refuted independently and completely,
but the refutation is already public** — scooped by two August 2026 arXiv papers.
Per campaign rules (no credit for known/posted results), the outcome is recorded as
*rejected: scooped*, and the independent work is documented below for provenance only.

---

## 1. The target that fell — and why it yields no credit

**Source question.** MathDB record **371031** ("The closed-form conjecture for the
optimal Schatten norm constant for m matrices", status `open`, solutions `[]` as of
2026-10-26), sourced to:

> Q. Tang, S. Zhang, *Generalizing Lee's conjecture on the sum of absolute values of
> matrices*, arXiv:2510.16846 (2025), Linear Algebra Appl. **731** (2026) 196–204.

**Conjecture 3.1** (as stated in the paper, all p > 1, m ≥ 2): the best constant in

    || Σ_{k=1}^m A_k ||_p  ≤  c_p(m) || Σ_{k=1}^m |A_k| ||_p        (all n, all A_k ∈ M_n)

is

    c_p(m) = sqrt( x(x+m−1) ) / ( x^p + m − 1 )^{1/p},
    x = the unique positive solution of x^p = 2x + (m−1),

with the extremal conjectured to be the rank-one family A_k = u·x_k* with
⟨x_j, x_k⟩ = s for j ≠ k (the family that is sharp at p = 2, proved by Lin–Zhang).

**My independent refutation** (complete, certified, before finding the prior art):

- **Counterexample** (p = 5/4, m = 3, n = 3): three rank-one matrices
  A_k = u_k x_k*, where u_k, x_k ∈ Q[i]³ have **exactly rational unit norm**
  (verifiable in exact integer arithmetic; see `witness_exact.json`).
  The conjecture asserts ratio ≤ c_{5/4}(3) = 1.01075360837534…;
  the witness attains **ratio = 1.01906799113…** (excess ≈ 8.31×10⁻³).
- Also refuted at m = 2 (two-matrix case), p = 5/4 and p = 3/2, by the same method.
- **The violation is a 1 < p < 2 phenomenon**: sweeping the structured rank-one family
  (Gram-magnitude parameters ρ_u, ρ_x and phases), the sup ratio exceeds the conjectured
  constant at p = 1.1, 1.25, 1.5 (m = 2, 3, 4) and **converges to the conjectured
  constant as p → 2⁻**, with no violation observed at p ≥ 1.75 or p = 2.5.
  At p = 2 the formula is the proven sharp Lin–Zhang constant.
- **The paper's own analysis of its conjectured extremal family is correct**: with the
  corrected |A_k| (A_k = u x_k*, |A_k| = x̂_k x̂_k*), the sup over the shared-left-vector
  family reproduces the closed formula to 15 digits for every p tested. The refutation
  therefore **requires genuinely two-sided configurations** (different left vectors u_k),
  which the paper's heuristic did not search.
- **Exact certificate** (`certificate.py`): all data rational; M₁ = S*S and
  D = Σ|A_k| = Σ x_k x_k* are rational-entry complex-Hermitian 3×3 matrices;
  ‖S‖_{5/4}^{5/4} = Σ λ_i^{5/8} and ‖D‖_{5/4}^{5/4} = Σ δ_i^{5/4} with λ_i, δ_i algebraic
  (roots of real-rational cubics — verified the char polys have real coefficients);
  c^{5/4} = y^{5/2}/(2(y⁴+2)^{3/8}) with y the positive root of y⁵ − 2y⁴ − 2 (substitution
  x = y⁴), monotone by the symbolic derivative y^{3/2}(y⁴+5)/(2(y⁴+2)^{11/8}) > 0.
  Comparison executed via sympy certified root isolation + 80-digit mpmath interval
  evaluation: **certified gap LHS − RHS = +0.0357923** (error budget < 10⁻⁴⁰).
  Secondary check: 60-digit direct evaluation (`final_verify.py`).

**Why no credit.** Prior-art search (mandatory before claiming) found the conjecture
already refuted publicly:

1. **arXiv:2608.15558** — *A counterexample to the Tang–Zhang Schatten norm conjecture
   and sharp positive results*: explicit real 2×2 rank-one matrices at p = 3/2, ratio
   above 207/200, certified by seven strict rational inequalities.
2. **arXiv:2608.18112** — *Counterexamples to a conjectured Schatten norm inequality*:
   disproves the formula **for every m ≥ 2 and every 1 < p < 2** — exactly the
   phenomenon found independently here (including the p → 2⁻ vanishing).

My p = 5/4 m = 3 witness is a new, independently derived, exactly-certified instance,
but it is an instance of a publicly refuted conjecture; under the campaign's counting
standard this earns nothing. Documented for honesty and provenance.

**Methodological notes worth keeping** (for future runs on Schatten-type problems):
- |u x*| = ‖u‖ · x̂x̂* (normalized projector, linear in ‖x‖) — easy to get wrong; two
  subtle wrong variants (x_k x_k* and x̂ x̂*) produce spurious huge "violations".
- The ratio ‖ΣA_k‖_p / ‖Σ|A_k|‖_p is invariant under (U,V) ∈ U(n)×U(n) gauge and common
  scaling, but **not** under per-k scaling; however near the extremal it is nearly flat
  in per-k scales (gradient ~10⁻⁵ per 2% scale change).
- For 1 < p < 2 the extremal breaks the S_m symmetry of the problem; symmetric
  (cyclic/equiangular) ansätze cap at the trivial or the conjectured value.
- Rational-unit-vector projection (stereographic map r ↦ (2r, 1−|r|²)/(1+|r|²) with
  rational r) converts any numerical witness into an exactly rational, exactly
  unit-norm one — the key step making algebraic certificates possible.

---

## 2. All other targets examined this run (verdicts)

| MathDB | Topic | Verdict |
|---|---|---|
| 373707 | oddzeroentry matrix, Conj 5 (2603.18253) | **KILLED**: the paper's own proof of its Thm 5 nowhere uses distinctness of x_i/y_i; 300k random repeated-pattern instances show zero violations (ratio ≤ 1 exactly). The "residue" is already settled by the source's Lemma 3.8 argument. Not a discovery. |
| 369189 | Liu–Cheng reverse log-majorization (2507.05242) | **KILLED**: fully resolved in public literature — Shi–Wei–Wang (LAA 739, 2026) prove q ≤ 2p; Trung (arXiv:2607.01263) gives the sharp hyperbola r ≤ pq/(q−2p) for q > 2p with explicit 3×3 counterexamples. No residue. |
| 332493 | four-projection trace inequality | **HOLDS** (screened hard): extensive complex random search over all rank configurations with Moore–Penrose constructions; min margin ≈ 4.7×10⁻⁴ > 0. Not a refutation target. |
| 361461 | Bourin–Lee Conj 3.2 (2401.05456) (same as MathDB 365564) | **HOLDS** (screened): derived von Neumann necessary condition; large searches n = 3–5, m = 2–4, p ∈ [0.5, 6]; all partial-sum margins decisively negative. |
| 362175 | weighted-Frobenius commutator (2403.04199, LAA 700) | **TRUE and exactly tight** after fixing two superoperator-reduction algebra traps; 120k trials + Powell on ω = diag(1,2,t) sit at the conjectured constants to 10⁻¹⁵, matching the paper's equality case. Not a refutation target. |
| 361693–96 | Lu–Wenzel / DDVV cluster | **TRUE/tight**: T_X superoperator formula verified to 10⁻¹⁴; λ₁+λ₃(T_X) → 3.0; GLZ even-sum S_k hits 2k+2 exactly; factor-2 LW clean. (Earlier apparent violation was a missing hypothesis — Conj 4.9 needs both Frobenius orthogonality and tr(B_α[B,B_β]) = 0.) |
| 372905 | sharp 3-operator Clarkson | **No violation** at p = 3, 4; p = 2.5 run blew up numerically (6×10¹⁴, optimizer artifact) — unresolved but no evidence of violation. |
| 406427 | Lin–vdD compression | **No violation** at p = 1, 1.5, 2. |
| 371031 | Tang–Zhang closed form | **REFUTED, but scooped** — see §1. |
| 375342/3, 380287, 405532, 324727, 355466, 367551 | various | Fetched; 405532 is `claimed_solved`; 380287 has 1 solution; the rest are operator/trace-theoretic conjectures (Kantorovich for 2-positive maps, all-order trace derivative positivity, noncommutative power-sum kernel) requiring deep theory, not screenable by search in remaining budget. **Left unexamined — honest gap.** |

**Not re-screened (known dead from root ledger):** 332939, 332318, 375999, plus the 21
accepted outcomes.

## 3. Gaps / what a continuation should do

- The unexamined list above (324287 BMV, 324727, 329181, 329636, 336251, 342339,
  351613/614, 355466, 359049, 360938/9, 361460, 365563/5/6, 367551, 369147, 370004,
  372758) — none touched numerically this run.
- The 372905 p = 2.5 numerical blowup was never resolved.
- If a lane wants a *cheap* strong result: the rational-unit-vector + algebraic-certificate
  pipeline built here (`build_exact.py` → `certificate.py`) is reusable for any
  finite-dimensional Schatten/Schur-type conjecture refutation.

## 4. Artifacts (in this directory)

- `witness_exact.json` — exact rational witness (u_k, x_k columns, exactly unit norm).
- `certificate.py` — exact algebraic certificate (run: `python3 certificate.py`).
- `final_verify.py` — 60-digit mpmath direct verification.
- `build_exact.py` — witness construction pipeline (from `witness_u_rational.npy` /
  `witness_x_rational.npy`, the rounded optimum of the structured family search,
  `best_fam4.pkl`).
