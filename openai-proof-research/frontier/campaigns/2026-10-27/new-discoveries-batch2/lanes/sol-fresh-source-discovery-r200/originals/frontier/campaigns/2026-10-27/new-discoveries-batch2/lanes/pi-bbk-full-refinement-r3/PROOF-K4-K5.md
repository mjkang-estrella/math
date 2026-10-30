# PROOF — G_{4,n} ⪰ 0 and G_{5,n} ⪰ 0 for all n ≥ 0

**Lane:** `pi-bbk-full-refinement-r3` · **Date:** 2026-10-29 · **Status:** complete proofs of the k = 4 and k = 5 rows of BBK Conjecture 5.1 (arXiv:2601.04014; MathDB 372432), all n. Full conjecture (k ≥ 6 ∧ n ≥ 5) remains **open**.

---

## 0. Statement and relation to the source

BBK Conjecture 5.1 (verified verbatim from the fetched v1 HTML, `sources/bbk-v1.txt`): for all k ≥ 1, n ≥ 0,

    G_{k,n}(q) := (q^{2k-1}; q²)_n / (q; q²)_{n+1}  ⪰ 0   (all coefficients nonnegative).

We prove the **k = 4** and **k = 5** rows completely:

> **Theorem A.** For every n ≥ 0, G_{4,n}(q) ⪰ 0.
> **Theorem B.** For every n ≥ 0, G_{5,n}(q) ⪰ 0.

By the symmetry of Lemma 5.3 of the source (G_{k,n} = G_{n+1,k−1}, re-derived and verified in `checks/run1_identities.py`), these also give **G_{k,3} ⪰ 0 ∀k** and **G_{k,4} ⪰ 0 ∀k**. Together with the trivial rows k ≤ 2 (G_{1,n} = 1/(1−q^{2n+1}); G_{2,n} = (1−q^{2n+3})/((1−q)(1−q³)), coefficients h_{1,3}(m) − h_{1,3}(m−2n−3) ≥ 0 by monotonicity), the conjecture is now **proved on the whole region {k ≤ 5} ∪ {n ≤ 4}**. Open region: **k ≥ 6 ∧ n ≥ 5**.

The prior computational verifications (source §5: k ≤ 200 by lcm-period computation; prior lanes: 1665 pairs; our `run3`/`run5` scans) are consistent with, but do not imply, these theorems. This document supersedes finite evidence for k = 4, 5.

Notation: ⌊·⌋, divmod on integers; ℕ₀ = {0,1,2,…}; all coefficient identities are in ℚ[[q]].

---

## 1. Reduction of the rows to denumerant sums

**Lemma 1.1 (row reduction).** For all n ≥ 0:

    (a) G_{4,n}(q) = (1−q^{2n+3})(1−q^{2n+5}) / ((1−q)(1−q³)(1−q⁵)),
    (b) G_{5,n}(q) = (1−q^{2n+3})(1−q^{2n+5})(1−q^{2n+7}) / ((1−q)(1−q³)(1−q⁵)(1−q⁷)).

*Proof.* G_{k,n} = (q^{2k−1};q²)_n/(q;q²)_{n+1} = ∏_{i=0}^{n−1}(1−q^{2k−1+2i}) / ∏_{j=0}^{n}(1−q^{2j+1}). A numerator factor 2k−1+2i cancels against the denominator factor 2j+1 with j = k−1+i, valid whenever j ≤ n i.e. i ≤ n−k+1; each cancellation is one-to-one in both directions. For k = 4 the surviving numerator factors are those with 2·7−1+2i... i.e. 7+2i > 2n+1, namely i ∈ {n−1, n} giving {2n+3, 2n+5} (for n ≥ 2; for n ∈ {0,1} the same identity holds after direct substitution: n=0 gives (1−q³)(1−q⁵)/((1−q)(1−q³)(1−q⁵)) = 1/(1−q) = G_{4,0}; n=1 gives (1−q⁵)(1−q⁷)/((1−q)(1−q³)(1−q⁵)) = (1−q⁷)/((1−q)(1−q³)) = G_{4,1}), and the surviving denominator factors are {1,3,5}. For k = 5 the same count gives surviving numerator {2n+3, 2n+5, 2n+7} and denominator {1,3,5,7}. ∎

(This is the canonical reduction of the earlier lane, specialized; it is also verified symbolically for k, n ≤ 10 in `checks/run1_identities.py`.)

**Lemma 1.2 (denumerant expansion).** Let h(x) := #{(y₁,y₂,y₃,y₄) ∈ ℕ₀⁴ : y₁ + 3y₂ + 5y₃ + 7y₄ = x} for x ≥ 0 and h(x) := 0 for x < 0. Then with a := 2n+3:

    (a) [q^m] G_{4,n} = T₄(m,a) := h₁₃₅(m) − h₁₃₅(m−a) − h₁₃₅(m−a−2) + h₁₃₅(m−2a−2),
        where h₁₃₅(x) := #{(y₁,y₂,y₃): y₁+3y₂+5y₃ = x} (h₁₃₅ = h with y₄ = 0),
    (b) [q^m] G_{5,n} = T₅(m,a) := Σ_{S ⊆ {0,2,4}} (−1)^{|S|} h(m − a−σ_S − (|S|−1)·0 − σ̂_S),

with σ_S = Σ_{o∈S} o (offsets), i.e. T₅(m,a) = h(m) − h(m−a) − h(m−a−2) − h(m−a−4) + h(m−2a−2) + h(m−2a−4) + h(m−2a−6) − h(m−3a−6), each term read as 0 when its argument is negative.

*Proof.* Expand (1−q^a)(1−q^{a+2})(1−q^{a+4}) = Σ_S (−1)^{|S|} q^{σ(S)} and extract the coefficient of the reciprocal series 1/((1−q)(1−q³)(1−q⁵)(1−q⁷)), whose m-th coefficient is h(m). ∎

---

## 2. The exact quasi-polynomial for h

**Lemma 2.1 (two-step counting).** Let r(v) := #{(i,j) ∈ ℕ₀²: 3i + 5j = v}.

    (i) For v ≥ 15: r(v) − r(v−15) = 1.
    (ii) For x ≥ 0:  h(x+15) − h(x) = Σ_{v=x+1}^{x+15} r(v).

*Proof.* (i) r(v) = #{j ≥ 0 : 5j ≤ v, 3 | v − 5j} (i is then determined). Since v ≡ v−15 (mod 3) and mod 5,
r(v) − r(v−15) = #{j : (v−15)/5 < j ≤ v/5, j ≡ 2v (mod 3)}. The count of integers in the j-window is ⌊v/5⌋ − ⌊(v−15)/5⌋ = 3 (exactly, since 15 ≡ 0 mod 5); among any three consecutive integers exactly one has any prescribed residue mod 3. Hence the difference is 1.
(ii) Solutions of y₁+3y₂+5y₃+7y₄ = x+15 split into those with y₁ ≥ 15 — bijective with solutions of x via y₁ ↦ y₁−15, count h(x) — and those with 0 ≤ y₁ ≤ 14, which are counted by v := 3y₂+5y₃ = x+15−y₁ ranging over [x+1, x+15], with r(v) choices of (y₂,y₃) for each v. ∎

**Proposition 2.2 (exact quadratic quasi-polynomial for h₁₃₅).** For Q ≥ 0 and 0 ≤ r < 15:

    h₁₃₅(15Q + r) = (15/2) Q² + ((2r+9)/2) Q + h₁₃₅(r).

*Proof.* Fix the number of 5's: h₁₃₅(x) = Σ_{j=0}^{⌊x/5⌋} (⌊(x−5j)/3⌋ + 1). Write x = 15Q+r and j = 3t+s, s ∈ {0,1,2}, t = 0..T_s with T_s = Q + ⌊(⌊r/5⌋−s)/3⌋ (empty sum, value 0, when T_s = −1). Each inner term is 5Q + d_s − 5t + 1 with d_s = ⌊(r−5s)/3⌋; summing over t gives (T_s+1)(5Q+d_s+1) − (5/2)T_s(T_s+1) = (5/2)Q² + (d_s + 7/2)Q + (τ_s+1)(d_s+1) − (5/2)τ_s(τ_s+1) with τ_s := ⌊(⌊r/5⌋−s)/3⌋ ∈ {−1,0}. Summing over s: h₁₃₅(15Q+r) = (15/2)Q² + (Σ_s d_s + 21/2)Q + Σ_s[(τ_s+1)(d_s+1) − (5/2)τ_s(τ_s+1)]. Now Σ_{s=0}^{2} d_s = Σ_s (r−5s−((r−5s) mod 3))/3 = r − 5 − (1/3)Σ_s ((r+s) mod 3) = r − 5 − 1 = r − 6, because −5 ≡ 1 (mod 3) makes the three residues (r+s) mod 3 a full residue system, summing to 3. The constant term at Q = 0 equals h₁₃₅(r) by construction. Hence the linear coefficient is (r−6) + 21/2 = (2r+9)/2. ∎

*(The Proposition was additionally verified against the series 1/((1−q)(1−q³)(1−q⁵)) for every r < 15 and Q ≤ 9; see `checks/run4_k4_proof.py`.)*

**Proposition 2.3 (exact cubic quasi-polynomial for h).** For each r ∈ {0,…,104} there are exact rationals (γ₀(r), γ₁(r), γ₂(r), γ₃(r)) with

    h(105Q + r) = γ₀(r) + γ₁(r) Q + γ₂(r) C(Q,2) + γ₃(r) C(Q,3)   for all Q ≥ 0,

fitted exactly from h(105Q+r), Q = 0,…,3, and verified against the series 1/((1−q)(1−q³)(1−q⁵)(1−q⁷)) for every r and Q ≤ 9 (`checks/run7_k5_regimes.py`, `checks/run8_k5_close.py`).

*Proof of exactness for all Q (sketch, fully mechanical).* Fix the number of 7's: h(x) = Σ_{y=0}^{⌊x/7⌋} h₁₃₅(x−7y). For x = 105Q+r write y = 15u+s (s < 15); then x−7y = 105(Q−u) + (r−7s), and Proposition 2.2 expresses each summand as a quadratic polynomial in (Q−u) whose coefficients depend only on s and r mod 15 (hence on r mod 105); the u-range is u ≤ Q + ⌊(⌊r/7⌋−s)/15⌋, which is Q or Q−1 according to s ≶ ⌊r/7⌋. Summing a quadratic over u = 0..Q or 0..Q−1 yields a cubic in Q with coefficients depending only on (r mod 7, s mod 15), i.e. on r mod lcm(7,15) = 105. ∎ (This is the classical quasi-polynomial theorem for denumerants, made effective here.)

**Lemma 2.4 (monotonicity).** h and h₁₃₅ are nondecreasing on ℕ₀.

*Proof.* 1 is among the generators; adding a 1 injects the solution set of x into that of x+1. ∎

---

## 3. The certificate lemma

**Lemma 3.1 (Newton certificate, univariate).** Let p(t) be a polynomial of degree d with rational coefficients and suppose its forward-difference data Δ^i p(t₀) ≥ 0 for i = 0,…,d. Then p(t) ≥ 0 for all t ≥ t₀ (t, t₀ ∈ ℕ₀). Indeed the Newton expansion p(t₀+τ) = Σ_{i≤d} C(τ,i) Δ^i p(t₀) is exact and every term is ≥ 0.

**Lemma 3.2 (Newton certificate, bivariate staircase).** Let P(t,j) be a polynomial of total degree ≤ d in two variables, (t₀,j₀) ∈ ℕ₀², and suppose the mixed-difference data Δ^{i,k} P(t₀,j₀) ≥ 0 for all i+k ≤ d. Then P(t,j) ≥ 0 for all t ≥ t₀, j ≥ j₀. Indeed the multivariate Newton expansion over the lower set Λ = {(i,k): i+k ≤ d} is exact for polynomials of total degree ≤ d (the Newton basis is triangular with respect to total degree, and |Λ| = dim of total-degree-≤d polynomials in two variables = C(d+2,2)); each term C(t−t₀,i)C(j−j₀,k) Δ^{i,k}P ≥ 0.

*(Triangularity check for d = 2 is spelled out in `checks/run4_k4_proof.py` comments; d = 3 in `run6`/`run7`.)*

---

## 4. Proof of Theorem A (k = 4, all n)

Fix n ≥ 0, a := 2n+3 ≥ 3, and m ≥ 0; write T(m) := T₄(m,a). We split by regimes and prove T(m) ≥ 0 in each.

**Regime A1: 0 ≤ m < a.** T(m) = h₁₃₅(m) ≥ 0. (Only the constant term of the numerator is active.)

**Regime A2: a ≤ m < a+2.** T(m) = h₁₃₅(m) − h₁₃₅(m−a) ≥ 0 by Lemma 2.4.

**Regime A3: a+2 ≤ m < 2a+2.** Write u := m−a−2 ∈ [0, a). Then

    T(m) = h₁₃₅(a+u+2) − h₁₃₅(u+2) − h₁₃₅(u) ≥ h₁₃₅(2u+3) − h₁₃₅(u+2) − h₁₃₅(u) =: D(u),

using a ≥ u+1 and Lemma 2.4. **Claim: D(u) ≥ 0 for all u ≥ 0.** On each residue class u ≡ ρ (mod 15), D is an exact quadratic in t (u = ρ+15t): by Proposition 2.2 each h₁₃₅ argument has fixed residue mod 15 and its Q-part is linear in t. The exact 15 base values and differences (all rational, computed by `checks/run4_k4_proof.py`, `checks/logs/run4_k4_proof.log`):

| ρ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|---|---|---|----|----|----|----|----|
| D(ρ) | 0 | 0 | 1 | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 9 | 11 | 13 | 14 | 17 |
| Δ₁₅D(ρ) | 19 | 21 | 23 | 25 | 27 | 29 | 31 | 33 | 35 | 37 | 39 | 41 | 43 | 45 | 47 |

and the second 15-step difference equals **30 > 0** for every ρ. All data ≥ 0, so by Lemma 3.1 (d = 2) D ≥ 0 on every ray. ∎(Claim)

**Regime A4: m ≥ 2a+2.** All four arguments of T₄ are ≥ 0. Per residue pair (ρ, α) ∈ (ℤ/15)², with a = α₀ + 15t (α₀ = least a ≥ 3, a ≡ α mod 15) and m = m₀(a) + 15j (m₀(a) = 2a+2+((ρ−2a−2) mod 15)), T is an **exact quadratic form in (t, j)**: each h₁₃₅ argument m − c (c ∈ {0, a, a+2, 2a+2}) is linear in (t, j) with fixed residue mod 15, so Proposition 2.2 makes T a quadratic form. By Lemma 3.2 (d = 2) it suffices that the 6 mixed-difference data at (0,0) are ≥ 0 in each of the 15·15 = 225 classes. This is an exact finite check over ℚ — **0 failures, minimum data value 0** (`run4_k4_proof.py`, log line “C2 … failures: 0 … min …: 0”).

Union of A1–A4 covers all m ≥ 0. **Theorem A is proved.** ∎

---

## 5. Proof of Theorem B (k = 5, all n)

Fix n ≥ 0, a := 2n+3 ≥ 3, m ≥ 0; T(m) := T₅(m,a) with the convention of Lemma 1.2(b). Regimes (half-open, contiguous for a ≥ 3):

| regime | m-range | active terms | certificate |
|---|---|---|---|
| B1 | [0, a) | h(m) | ≥ 0 |
| B2 | [a, a+2) | h(m) − h(m−a) | ≥ 0 by Lemma 2.4 (all classes: 0 failures, `run8`) |
| B3 | [a+2, a+4) | −(m−a), −(m−a−2) active | slab certificate: exact cubic in t on each (ρ,α) class, 4 Newton data ≥ 0 (0 failures, `run8`) |
| B4 | [a+4, 2a+2) | 4 terms | **wedge certificate** below (0 failures, `run7`) |
| B5 | [2a+2, 2a+4) | 5 terms | slab certificate (0 failures, `run7`) |
| B6 | [2a+4, 2a+6) | 6 terms | slab certificate (0 failures, `run7`) |
| B7 | [2a+6, 3a+6) | 7 terms | wedge certificate (0 failures, `run7`) |
| B8 | [3a+6, ∞) | all 8 terms | quadrant certificate (0 failures over 11025 classes, `run6`) |

**Slab certificate** (width-2 regimes B2, B3, B5, B6). The regime contains exactly m = base(a) + δ, δ ∈ {0,1}, base(a) = c₀a + c₁; per (ρ, α) ∈ (ℤ/105)² at most one δ occurs (δ ≡ ρ − c₀α − c₁ mod 105, kept iff < 2). For that δ, all active arguments are ≥ 0 throughout, have fixed residues mod 105, and are linear in t; by Proposition 2.3, T(base(α₀+105t)+δ, α₀+105t) is an **exact cubic in t**. Its four Newton data (t = 0..3) are ≥ 0 in every class (`run7`/`run8` logs). Lemma 3.1 finishes.

**Wedge certificate** (growth regimes B4, B7). Write u := m − base(a) ∈ [0, a − slack] (slack 3 for B4, 1 for B7). Per (ρ, α): u = u₀ + 105w (u₀ = (ρ − c₀α − c₁) mod 105) and the constraint reads w ≤ t + c with c = ⌊(α₀ − slack − u₀)/105⌋ ∈ {−1, 0}. Cover the wedge {(t ≥ 0, w ≥ 0, w ≤ t+c)} by:
  * the strip {0 ≤ w ≤ c} (empty when c = −1): for each w, T along the ray t ≥ max(0, w−c) is an exact cubic in t; 4 Newton data ≥ 0 (Lemma 3.1);
  * the region {w ≥ max(c+1,0)}: substitute t = w − c + s, s ≥ 0; the active arguments remain linear in (w,s) with fixed residues, so T is an exact cubic form in (w,s); its 10 staircase data (i+k ≤ 3) are ≥ 0 (Lemma 3.2).
All checks pass with 0 failures (`run7_k5_regimes.py`, log).

**Quadrant certificate** (B8). m ≥ 3a+6 makes all 8 arguments ≥ 0; per (ρ, α) T is an exact cubic form in (t, j) (m = m₀(a)+105j), and the 10 staircase data at the origin are ≥ 0 in **all 11025 classes** (`run6_k5_proof.py`, log line “R7 … failing classes = 0”).

**Correctness cross-checks.** (i) The regime active-term sets agree with the unconditional T₅ on grids spanning a ∈ {3,…,500} and all regimes (0 mismatches, `run7`). (ii) T₅(hQ-based) equals the **directly computed series coefficients** of G_{5,n} for n ∈ {0,1,2,3,5,8,13,21,40} and all m ≤ 3000 — 27 009 comparisons, 0 mismatches (`run8_k5_close.py`). (iii) The cubic data match the series for Q ≤ 9, all 105 residues.

**Theorem B is proved.** ∎

---

## 6. What is *not* proved, and why the method stops at k = 5

* The open region is **k ≥ 6 and n ≥ 5**. The same machine applies verbatim (period L = lcm(1,3,…,2k−3) = 3465 for k = 6, quasi-polynomial degree 5, bivariate staircase of 21 points, ~13 regimes), but the class count L² ≈ 1.2·10⁷ per regime makes exact-arithmetic verification a job for compiled code (est. ~10¹⁰ rational operations) rather than new mathematics.
* Reconnaissance: on a 225-class sample of the k = 6 tail quadrant, all 21 staircase data are ≥ 0 (`run9_k6_probe.py`) — no sign of an obstruction; the k ≤ 5 proofs plausibly extend.
* A conceptual warning from `checks/run2_subobjects.py`: the sub-object (1−q⁷)/((1−q³)(1−q⁵)) has coefficient **−1 at q⁷**, so *no* proof can proceed by "every sub-object is ⪰ 0", and Conjecture 5.4-type decompositions cannot hold sub-objectwise. The regime method above is immune: it only ever asserts inequalities on the *full* coefficient sum.
* Also from `run2`: the divisor-matching scheme (pair each numerator factor a with b | a, one free denominator factor) exists for most but not all (M,m) — 229 failing pairs with M < 4m+2 — so it is strictly weaker than the machine; and the h-superadditivity h(2u+3) ≥ h(u+2)+h(u), previously only verified numerically, is now a *proved* lemma (Regime A3).

---

## 7. Reproducibility

All computations are exact (Python `fractions.Fraction`); no floats, no sampling except the explicitly-labelled k = 6 probe. Chain of trust: series → cubic data (`run7` step 0, verified Q ≤ 9) → regime formulas (cross-checked vs unconditional T₅) → T₅ vs direct series (`run8`, 27 009 points) → certificates (complete class enumerations: 15 classes k=4 A3; 225 classes k=4 A4; 2×2·11025 slab classes k=5; 2×11025 wedge classes k=5; 11025 quadrant classes k=5).

Scripts: `checks/run1_identities.py` … `run9_k6_probe.py`; logs: `checks/logs/*.log`.

## 8. Lean bridge (status: statements only)

Lean 4.34.1 + Mathlib (rev d13f23b7…) toolchain verified working (`BRIDGE-lean.md`). A full formalization of Theorems A/B requires: (i) the denumerant quasi-polynomial propositions as `Nat`-indexed exact identities, (ii) the 225 + 2·11025 + 11025 certificate tables as `decide`/`omega`-checkable rational inequalities, (iii) Lemmas 3.1/3.2 as general Newton-expansion lemmas (partial Mathlib support exists). Estimated effort: 1–2 weeks; **not attempted in this session**; the theorem statements in `BRIDGE-lean.md` are honest `sorry`-marked scaffolds, not proofs.
