# Lane: pi-jacobi-shifted-content-discovery

**Status: no full theorem.** Verified reduction, extended exact verification, one new
precise conjecture (mod-2 unit law) that would imply the full law, structural laws, and
an honest obstacle map. **No PROOF.md** — the all-order result is not proved here.

## 1. Target (exact source statements)

Primary: Area, arXiv:2608.23006v2, Remark 3.8. Let δ_r be the exponent of 2 in the
common denominator of the coefficients of the formal phase constant κ_r (Definition 2.1)
written in the shifted variables u = µ_α = A − 1/4, v = µ_β = B − 1/4. Source bounds
(whenever the conditional top-layer identification (14) holds):
2r + ν2((r−1)!) ≤ δ_r ≤ Er = 3r − 1 + ν2((r−1)!). Open problem: determine δ_r.
Proposed law: **δ_r = 2r + ν2((r−1)!)**.

Excluded (already proved, never to be credited): companion arXiv:2609.29531
Theorem 1.5 / 7.36 (sharp law in (A,B): ν2([A¹B⁰]κ_r) = −Er), Theorems 1.1–1.4,
7.33–7.34, Section 10 valuation formulas (Legendre tangent = linear response only).
The companion's Section 11 cites, for the shifted polynomial, only the Er bound —
the shifted content is open in both papers. All work here concerns the formal
Definition 2.1 polynomial; the all-order identification with the actual phase
expansion is conditional in the source (checked r ≤ 8) and is not used.

## 2. Verified reduction (re-derived independently, analytically and computationally)

With P_l(w) = ∏_{j=0}^{l−1}(w − j(j+1)), p = 1+i, q = 1−i, x0 = p/2, y0 = q/2:

    F(Z) = Σ_{c,d≥0} P_c(u) P_d(v) x0^c y0^d /(c! d!) · 1/((Z−1)···(Z−(c+d))).

* Sign check: the x^c y^d coefficient of the amplitude (6) is
  a_c(α)a_d(β)(2x)^c(2y)^d with a_c(α) = (1/2±α)_c/((−2)^c c!), and
  (1/2±α)_c = (−1)^c P_c(u); the two sign layers cancel, giving exactly P_c(u)P_d(v).
* Expanding 1/((Z−1)···(Z−s)) = Z^{−s} Σ_k h_k(1,…,s) Z^{−k} and using the classical
  identity h_{n−s}(1,…,s) = S2(n,s) (Stirling, second kind; proved independently and
  machine-checked against a direct complete-homogeneous DP):

    A_n := 2^n n! [Z^{−n}] F = Σ_{m≤n} S2(n,m) 2^{n−m} (n!/m!) C̃_m,
    C̃_m = Σ_l binom(m,l) P_l(u) P_{m−l}(v) p^l q^{m−l},

  which is exactly the parent lane's reduction. (The parent's script effectively uses
  the conjugate convention p ↔ q; imaginary parts then change sign, contents and all
  min-ν2 statements are unaffected.)
* Cumulants: B_1 = A_1, B_n = A_n − Σ_{k=1}^{n−1} binom(n−1,k−1) B_k A_{n−k};
  equivalent to the standard n a_n = Σ_{k≤n} k b_k a_{n−k} for log F (checked on n ≤ 3
  by hand and machine-checked throughout). B_n = 2^n n! [Z^{−n}] log F.
* κ_r = Im B_{2r−1} / (2^{4r−2} (2r−1)!), so with m = r−1:

    **δ_r = 2r + ν2((r−1)!)  ⟺  min ν2(coefficients of Im B_{2m+1}(u,v)) = 3m.**

  (ν2((2r−1)!) = 2r−2−s2(r−1); algebra in progress.md.)
* Machine validation against every published value: den κ_1..κ_4 = 4, 96, 7680,
  86016 = 2^12·21 (Table 1) and ℓ_1..ℓ_4 = 1/4, −7/96, 781/7680, −28421/86016 (eq. (3)),
  computed from my independent pipeline. Scripts: `jacobi_shifted_core.py`,
  `verify_all.py`; results in `verification_results.json`.

## 3. New exact verification (beyond all published ranges)

All exact (Gaussian-integer / rational); no floating point.

1. **Content law** min ν2(Im B_{2m+1}) = 3m: **r ≤ 40** (parent lane had r ≤ 12;
   nothing published).
2. **Top-layer identification** (source Computational observation 3.1 / Prop 3.1,
   conditional there for r ≤ 20): [µ_α^r]κ_r = γ_r I_r with
   γ_r = 2·C(2r,r)/((2r−1)16^r) = C(2r−1,r−1)/((2r−1)2^{4r−2}) (I re-derived this
   closed form from exact data; it matches the arXiv HTML formula and the source's
   Kummer valuation ν2(γ_r) = 1+s2(r)−4r): verified **r ≤ 40**. Hence the pure
   coefficient has ν2 exactly 3(r−1) (attainment) through r = 40.
3. **NEW conjecture (mod-2 unit law)**, verified **m ≤ 30**:

       Im B_{2m+1}(u,v) ≡ 2^{3m} [ (u+v)^{m+1} + δ_{m≡1 (mod 4)} (u+v)^m ]
       (mod 2^{3m+1}).

   This single congruence implies the **full** law: divisibility (2^{3m} divides every
   coefficient) *and* attainment ((u+v)^{m+1} survives mod 2). It is the literal
   formal endpoint for a future proof.

## 4. Structural facts (new; elementary proofs or machine-verified)

* Im B_{2k} ≡ 0 identically (verified n ≤ 83).
* deg B_n = ⌈n/2⌉, hence deg Im B_{2m+1} = m+1 (verified n ≤ 83; consistent with the
  source's observation that κ_r has degree r for r ≤ 8).
* [u^n]A_n = p^n = (1+i)^n and [v^n]A_n = q^n — proved: only s = n contributes to
  degree n in A_n, and [u^n]C̃_n = [u^n]P_n(u)·p^n = p^n.
* content(Im C̃_s) ≥ ⌊s/2⌋ and content(Re C̃_s) ≥ ⌊s/2⌋ — elementary: for l ≤ s/2,
  p^l q^{s−l} = 2^l q^{s−2l}, and ν2(Im q^j), ν2(Re q^j) ≥ ⌊j/2⌋ − 1 with the product
  always ≥ 2^{⌊s/2⌋} on the nonzero terms.
* Consequently content(Im A_{2m+1}) = m with the minimum attained on the top
  homogeneous part (verified m ≤ 12): the cumulant recursion lifts the content from
  m to 3m. The entire difficulty is this global 2-adic cancellation — exactly the
  phenomenon the source warns about for ℓ_r and the companion isolates by the
  "exactly one minimal term" mechanism (Lemmas 7.30–7.33, Remark 10.6).
* No off-diagonal Z+4 difference equation: I computed
  G(v) = v²·Z(Z+2)·F(Z+4)/F(Z) exactly (v = 1/Z, 1/(Z+4) = v/(1+4v)). On the diagonal
  u = v = w it equals (1+v)² − 4(w+1/4)v²·... i.e. ((Z+1)²−4A)v² exactly
  (re-confirming companion Corollary 1.2), but off the diagonal the coefficients are
  non-real and do not terminate — so the diagonal difference-equation mechanism does
  not generalize; the companion's own off-diagonal relation is the three-term
  parameter relation (Theorem 7.1(35)).

## 5. Obstacles (honest)

* Divisibility 2^{3m} | Im B_{2m+1} is a global cancellation statement; term-by-term
  bounds give only Er (Theorem 1.2). The companion's isolation mechanism works because
  the linearized forcing F̂_Γ is an explicit exponential of a series with one minimal
  term (b_1 = −1, Genocchi valuations); the bivariate analogue of that explicit
  exponential is not available in the companion and I did not find one.
* The exact closed form (37)–(38) reduces F to
  2F1↑(σ+(β−α)/2, σ+(β+α)/2; 2σ; 2) with a+b = c+β. For β = 0 the split blocks are
  Gauss/Kummer summable (zero-balanced); for β ≠ 0 they are not, so the companion's
  Section 7.7/10 analysis does not extend verbatim.
* Induction on the cumulant recursion for the mod-2 unit law needs Im B_{2j+1} mod
  2^{3j+1+C} with growing precision C (the Re A_{2(m−j)} content bounds enter the
  target precision), i.e. a full mod-2^k asymptotic expansion of B_n — not completed.

## 6. What a full result requires (literal endpoint)

* **Theorem A (divisibility):** 2^{2r+ν2((r−1)!)} κ_r ∈ Z_2[µ_α, µ_β]  (all r ≥ 1).
* **Theorem B (attainment):** ν2([µ_α^r]κ_r) = −(2r + ν2((r−1)!)) — via the top-layer
  identification proved for all r, or any other attaining coefficient.
* Equivalent single endpoint: the mod-2 unit law of §3(3).

**Lean plan** (pinned Lean 4.34.1 / mathlib d13f23b7), only worth starting after A+B:
(i) reduction layer: Stirling identity h_{n−s}(1..s) = S2(n,s) (Mathlib has
`sophomore's dream`-adjacent Stirling API; else derive), cumulant recursion, the
κ_r-normalization and the δ_r ⟺ content-law equivalence — all elementary EDCF;
(ii) Gaussian-integer content lemmas (ν2 of Im(p^l q^j)); (iii) Theorems A, B.
The reduction is formalizable now; the law is not, until proved.

## 7. Novelty screen (bounded)

Both source papers read at the relevant sections (2608.23006v2 in full; 2609.29531:
§§7–8, 10–11, App. A headers). The companion contains no shifted-content result
(§11 cites only the Er bound; §10 is tangent-only; Prop 3.1 conditional). Web search
(2026-10-27, Exa) surfaces only these two papers and mirrors; no third paper, no
prior theorem subsuming δ_r. Under the campaign counting standard, everything in this
lane is **credit 0**: verified reductions, extended finite verifications, and a new
conjecture — no all-order theorem.

## 8. Files

* `scripts/jacobi_shifted_core.py` — independent pipeline (F, A_n, B_n, κ_r, γ_r, I_r).
* `scripts/verify_all.py` — consolidated checks; `verification_results.json` (also
  `scripts/verification_results.json`).
* `scripts/test_difference_equation.py` — off-diagonal Z+4 test (§4, last bullet).
* `progress.md`, `provenance.json`.
