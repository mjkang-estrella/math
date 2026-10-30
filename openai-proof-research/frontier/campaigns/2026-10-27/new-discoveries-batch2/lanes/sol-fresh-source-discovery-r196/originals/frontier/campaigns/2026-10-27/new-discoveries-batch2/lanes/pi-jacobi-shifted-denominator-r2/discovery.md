# Discovery — shifted-denominator law for κ_r (Area 2608.23006v2, Remark 3.8)

Lane: `pi-jacobi-shifted-denominator-r2` (solo sub-agent, batch2, 2026-10-27)
Status: **partial progress — two all-order structure theorems proved, the valuation law
itself reduced exactly to two explicit sub-statements, not closed.**

---

## 0. Target and conventions

Source (verified live v2 on 2026-10-27, cached text matches):
arXiv:2608.23006v2. Definition 2.1 defines formal polynomials
κ_r ∈ Q[x, y, µ_α, µ_β] by κ_r = 2^{−(2r−1)} Im L_{2r−1}(x₀, y₀) with
x₀ = (1+i)/2, y₀ = (1−i)/2; Remark 3.8 states
2r + ν₂((r−1)!) ≤ δ_r ≤ 3r−1+ν₂((r−1)!) with gap r−1 and asks for the exact δ_r,
where δ_r is the exponent of 2 in the common denominator of the coefficients of κ_r
**in the shifted variables** u = A − 1/4, v = B − 1/4, µ_α = 1/4 − α, µ_β = 1/4 − β.

The companion arXiv:2609.29531v2 proved the **original-variable** law
E_r = 3r−1+ν₂((r−1)!) (its Theorem 1.2/1.3). The shifted question is exactly the
source's open Remark 3.8 and is *not* covered by the companion (its §11 says so).

**Working object.** Write L(Z; u, v) = Σ_{n≥1} B_n(u,v) Z^{−n} / (2^n n!) for the
log of the termwise polynomial part of the double series; concretely (this is the
old lane's machine-verified reduction, re-derived here in `scripts/core.py`):

- P_c(t) := Π_{j<c}(t − j(j+1)) ∈ Z[t], P_0 = 1;
- C̃_m(u,v) := Σ_{l≤m} binom(m,l) P_l(u) P_{m−l}(v) p^l q^{m−l}, p = 1+i, q = 1−i;
- A_n(u,v) := Σ_{s≤n} S₂(n,s) 2^{n−s} (n!/s!) C̃_s(u,v)  (= 2^n n! [Z^{−n}] of the double series);
- B_1 = A_1, B_n = A_n − Σ_{k<n} binom(n−1,k−1) B_k A_{n−k} (cumulant recursion);
- κ_r = Im B_{2r−1} / (2^{4r−2} (2r−1)!), a polynomial in (u,v).

**The reduction (re-derived and machine-verified here, m = r−1):**

> δ_r = 2r + ν₂((r−1)!)  ⟺  min{ ν₂(c) : c ranges over all coefficients of Im B_{2m+1}(u,v) } = 3m,

using ν₂((2r−1)!) = 2r−2−s₂(r−1) and ν₂((r−1)!) = r−1−s₂(r−1).
(Check of the bookkeeping: κ₂ = Im B₃/384 = (u−v)(u+v−3)/48 has δ₂ = 4 = 2·2+ν₂(1!);
in original variables κ₂ = (A−B)(A+B−7/2)/48, coefficients with denominator 2⁵·3,
matching the published ℓ₂ = −7/96 and E₂ = 5. All published κ₁..κ₄/ℓ₁..ℓ₄ data match
this pipeline.)

Everything below is about Im B_{2m+1} ∈ Z[u,v], m ≥ 0.

## 1. Theorem 1 (Antisymmetry; even cumulants vanish) — **proved, all order**

> **Theorem 1.** For every n ≥ 1, B_n(v, u) = conj(B_n(u, v)) coefficientwise
> (conj applied to the Gaussian-integer coefficients). Equivalently: the real part of
> B_n is symmetric under u↔v and Im B_n is antisymmetric. Consequently
> (i) Im B_{2k} = 0 for all k ≥ 1 (even cumulants are real polynomials);
> (ii) (u−v) | Im B_n in Z[u,v] for all n;
> (iii) L(Z;v,u) = conj(L(Z;u,v)) and F(Z;v,u) = conj(F(Z;u,v));
> (iv) F(Z;u,v)·F(−Z;u,v) ∈ R[[Z^{−1}, µ_α, µ_β]] — the even part of L has real
> coefficients and the antisymmetric part is supported on odd powers of Z^{−1}.

*Proof.* The double series behind A_n is
F(Z; u,v) = Σ_{c,d ≥ 0} P_c(u) P_d(v) (p/2)^c (q/2)^d h_{c+d}(Z) / (c! d!)
with h_k(Z) = 1/(Z−1)_k ∈ Z[Z^{−1}] real (the termwise polynomial part; the sign
convention of the source is absorbed in the definition of P_c). All coefficients of
P_c, P_d are integers; p = conj(q); h real. Swapping the two summation indices,

F(Z; v,u) = Σ_{c,d} P_c(u) P_d(v) (q/2)^c (p/2)^d h_{c+d}(Z)/(c!d!) = conj(F(Z; u,v)),

coefficientwise in Z^{−1} and in (u,v). Since F has constant term 1 and is invertible
as a formal series, taking −log termwise (the cumulant recursion is exactly the
termwise log: B_n = 2^n n! [Z^{−n}] log F) preserves the identity:
L(Z; v,u) = log F(Z; v,u) = conj(log F(Z; u,v)) = conj(L(Z; u,v)). Hence
B_n(v,u) = conj(B_n(u,v)). (ii): Im B_n(u,v) = (B_n(u,v) − B_n(v,u))/(2i) is
antisymmetric under u↔v, hence vanishes on the diagonal and is divisible by u−v;
it lies in Z[u,v] because B_n ∈ Z[i][u,v]. (iii) is the identity just proved; (iv):
log(F(Z)F(−Z)) = L(Z) + L(−Z) = Σ_n (1+(−1)^n) B_n Z^{−n}/(2^n n!) contains only
even powers, while F(Z)F(−Z) has real coefficients by (iii) applied twice. ∎

**Corollary 1.1.** Im B_{2k} = 0 for all k ≥ 1 (verified independently to n ≤ 61).

**Corollary 1.2.** Im g_{2k} = 0 for all k ≥ 1, where g_n = ∂L_n/∂A(x₀,y₀)|_{A=B=0}
is the companion's one-parameter response object. Indeed Im g_{2k} is, up to the real
factor 2^{2k}(2k)!, the u¹-coefficient of B_{2k}, which is real by Theorem 1(i).
This re-derives the companion's Theorem 1.5 by pure algebra, and strengthens it: the
vanishing holds for the full polynomial B_{2k} at *all* (u,v), not merely its
A-derivative at the Legendre point.

**Corollary 1.3 (normal form).** Im B_{2m+1}(u,v) = (u−v) Q_{2m+1}(u,v) with
Q_{2m+1} ∈ Z[u,v] **symmetric** (Q(u,v) = Q(v,u)) and deg Q_{2m+1} = m.
(The antisymmetry gives divisibility by u−v; the quotient of an antisymmetric
polynomial by u−v is symmetric.)

*Proof of Corollary 1.3's integrality is immediate; symmetry: (u−v)Q antisymmetric
⟹ Q(v,u)(v−u) = −(u−v)Q(u,v) ⟹ Q(v,u) = Q(u,v). ∎*

*Verification:* antisymmetry of Re/Im parts and the normal form checked
coefficientwise for n ≤ 61 (`scripts/decomposition.py`, `verification_results.json`).

## 2. Theorem 2 (Exact one-center / coupling decomposition) — **proved, all order**

> **Theorem 2.** For every m ≥ 0 there exist unique polynomials
> R_{2m+1} ∈ Z[u,v], symmetric, of degree ≤ m−1 (R = 0 for m ≤ 1), such that
>
>   Im B_{2m+1}(u,v) = [ ImB_{2m+1}(0,v) − ImB_{2m+1}(0,u) ] + u v (u−v) R_{2m+1}(u,v).
>
> Consequently **every pure coefficient of Im B_{2m+1} is a coefficient of the
> one-center slice**: [u^j] Im B_{2m+1} = −[v^j] Im B_{2m+1}(0,v) and
> [v^j] Im B_{2m+1} = [v^j] Im B_{2m+1}(0,v); and every mixed coefficient
> (both u,v-exponents ≥ 1) is a coefficient of uv(u−v)R_{2m+1}.

*Proof.* Define K_{2m+1} := Im B_{2m+1} − W with W(u,v) := ImB_{2m+1}(0,v) −
ImB_{2m+1}(0,u). Then W is antisymmetric; K is antisymmetric (Theorem 1);
K(0,v) = 0 by construction and K(u,0) = ImB(u,0) + ImB(0,u) = 0 by antisymmetry.
An antisymmetric polynomial in Z[u,v] vanishing on both axes is divisible by
uv(u−v) — write K = uv·M; antisymmetry of K forces M antisymmetric; M = (u−v)R with
R symmetric; primitivity of uv(u−v) gives R ∈ Z[u,v]. ∎

**Interpretation (mechanism, uses the companion's published Corollary 8.2).** The
companion's conjugate-layer factorization writes F = (layer 0)·(1 + Σ_{r≥1} R_r)
with layer 0 = P_0(µ_α;Z)·P̄_0(µ_β;Z) the product of the two one-center Gauss
functions and R_r = O(Z^{−3r}). Taking −log termwise:
- the layer-0 contribution to Im B_n is exactly ω_n(u) − ω_n(v) where
  ω_n(t) := 2^n n! Im [Z^{−n}] log P_0(µ_t; Z) is the one-center slice polynomial;
  this equals W above (since ImB_n(0,v) = ω_n(0) − ω_n(v), layers dying at µ_α = 0
  because γ_r(1/4) = P_r(0) = 0, r ≥ 1);
- K_{2m+1} is exactly the total contribution of layers r ≥ 1, and receives layers
  r ≤ ⌊(2m+1)/3⌋ only.

So Theorem 2 is the statement "layers ≥ 1 are divisible by uv(u−v)", which is
elementary; the deep content is their 2-adic size (Theorem 3B below).

## 3. Theorem 3 (Exact reduction of Remark 3.8) — **proved, all order**

> **Theorem 3.** Let m ≥ 0. The following are equivalent:
> (Law)  min ν₂ over coefficients of Im B_{2m+1} equals 3m  [⟺ δ_{m+1} = 2(m+1)+ν₂(m!)];
> (A)  **one-center slice law**: every coefficient of Im B_{2m+1}(0,v) is divisible by
>      2^{3m}, and the coefficient [v^{m+1}] of the slice is exactly 2^{3m} × odd;
> (B)  **coupling divisibility**: 2^{3m} | R_{2m+1}(u,v) (all coefficients).
>
> Moreover, under (A) the minimum 3m is **attained at the pure coefficients**
> [u^{m+1}], [v^{m+1}] of Im B_{2m+1} regardless of K.

*Proof.* (⟸) Divisibility: pure coefficients are slice coefficients (Theorem 2), ≡ 0
mod 2^{3m} by (A); mixed coefficients are uv(u−v)R-coefficients, ≡ 0 mod 2^{3m} by
(B). So min ν₂ ≥ 3m. Attainment: [u^{m+1}]ImB_{2m+1} = −[v^{m+1}]slice = −2^{3m}·odd
by (A) (the uv(u−v)R part has no pure monomials), so the minimum is exactly 3m.
(⟹) (A) is the restriction of the Law to pure coefficients, which are ± slice
coefficients (Theorem 2); (B) is the restriction to mixed coefficients, which are
uv(u−v)R-coefficients and uv(u−v) has unit content. ∎

This is, to our knowledge, **new**: the bivariate open problem in Remark 3.8 is now
exactly equivalent to a *one-variable* statement about the single Gauss-function log
(the slice, α fixed at 1/2, β free) plus a divisibility statement about the
symmetric "coupling" polynomial R_{2m+1} = K/(uv(u−v)).

## 4. Verified statements (fresh exact pipeline, `scripts/`, Python 3.14.8 sympy 1.14)

All exact integer arithmetic; ranges: n ≤ 61 (i.e. m ≤ 30, r ≤ 31) unless noted.

| # | Statement | Range | Status |
|---|---|---|---|
| V1 | min ν₂(ImB_{2m+1}) = 3m (the Law) | m ≤ 30 | verified (old lane: r ≤ 40) |
| V2 | ImB_{2k} = 0 | n ≤ 61 | **proved** (Thm 1) + verified |
| V3 | Re/Im antisymmetry B_n(v,u) = conj B_n | n ≤ 61 | **proved** (Thm 1) + verified |
| V4 | (u−v) \| ImB_n; quotient Q symmetric | m ≤ 30 | **proved** (Thm 1) + verified |
| V5 | ImB_{2m+1} = W + uv(u−v)R, R symmetric integral | m ≤ 30 | **proved** (Thm 2) + verified |
| V6 | slice law (A): 2^{3m} \| slice, [v^{m+1}] = 2^{3m}·odd | m ≤ 30 | verified |
| V7 | coupling divisibility (B): 2^{3m} \| R_{2m+1} | m ≤ 30 | verified |
| V8 | refined: min ν₂(K_{2m+1}) = 3m + 1_{m=2^k−1} (k≥2) | m ≤ 30 | verified pattern (m=3,7,15 exceptional; m=0,1 K=0) |
| V9 | deg B_n = ⌈n/2⌉ | n ≤ 61 | verified (conjecture) |
| V10| deg ImB_{2m+1} = m+1; deg K = m+1; deg R = m−1 | m ≤ 30 | verified |
| V11| top layer (14): [u^{m+1}]ImB_{2m+1} = 2^{4r−2}(2r−1)! γ_r I_r, γ_r = 2C(2r,r)/((2r−1)16^r) | r ≤ 31 | verified (old lane r ≤ 40) |
| V12| normal form ImB_{2m+1} = 2^{3m}(u−v)Q̃, Q̃ ≡ (u+v)^m + 1_{m≡1(4)}(u+v)^{m−1} (mod 2) | m ≤ 30 | verified (old lane m ≤ 30) |

Note on V8: the exceptional set {2^k−1} is exactly where binom(2m+1, m) is odd —
suggesting the coupling minimum is governed by a binomial-coefficient parity, the
same way the source's Theorem 1.4 valuation (m + ν₂(m+1)) is.

## 5. Why this is progress, and what is still open

**Progress over the 2026-10-26 lane** (which verified V1/V12 to r ≤ 40 but proved
nothing all-order): this lane *proves* all-order structural theorems (V2–V5) and
*exactly reduces* the open Remark 3.8 to (A)+(B). It also kills a class of attempted
proofs: any argument that treats the coefficients of ImB_{2m+1} termwise (e.g. via
the (13)-mechanism alone) cannot see the cumulant gain 2m (the (13) terms only give
content m); Theorem 1–2 show the true mechanism must combine the log (cumulant)
structure with the u↔v conjugate pairing.

**Open.** Two statements remain:
- **(A) one-center slice law** — min ν₂ of ImB_{2m+1}(0,v) = 3m with the
  [v^{m+1}] coefficient a 2^{3m}-unit. This is a one-variable cumulant problem for
  log ₂F₁(1/2−β, 1/2+β; 1−Z; y₀). Candidate route: a transfer identity in the style
  of the companion's §4 (Borel transform Φ(t), convolution with sinh2t/2t,
  τ-preserving lemmas) adapted to the one-center imaginary parts; the companion's own
  Legendre-point mechanism (their §10: Den = exp Λ, d±_n valuations) proves exactly
  this type of statement at µ_α = µ_β = 0, but the bivariate/one-center version needs
  the β-dependent Γ-ratio expansions, whose valuations are β-dependent — the
  polynomial nature of the statement must absorb them.
- **(B) coupling divisibility** 2^{3m} | R_{2m+1}. Layer analysis (companion §8–9,
  eq. (92)): layer r carries prefactor 2^{−r−ν₂(r!)} and P_r(µ_α)P_r(µ_β) with the
  ratio expansions P_r/P_0 differing from 1 by multiples of 2^{ν₂(r)}-ish; the crude
  bound gives ≥ 4m+1−s₂(m)−r−ν₂(r!) + … which does **not** reach 3m without using the
  imaginary-part structure (the x₀/y₀ asymmetry between the α and β factors). A
  proof of (B) likely needs a bivariate version of the companion's §10 valuation
  transfer — the natural next step, and the piece the companion explicitly leaves
  open (its §11).

**What would complete a proof:** prove (A) and (B) for all m. Then δ_r =
2r+ν₂((r−1)!) follows by Theorem 3 with the formal Lean skeleton below.

## 6. Formalization readiness

No `PROOF.md`: Theorem 3 is conditional on (A), (B). A Lean 4.34.1 + Mathlib
(d13f23b) skeleton for Theorems 1–3 is feasible (all statements are finite
combinatorial polynomial facts: Gaussian-integer polynomial antisymmetry, cumulant
recursion, divisibility); it was **not** written because the target law itself is
unproved, and a skeleton proving only the reduction would not satisfy the acceptance
gates. The proof of Theorems 1–3 is fully self-contained in §1–3 above (≈ half a
page each) and formalizes mechanically.

## 7. Negative results / dead ends (this lane)

- Off-diagonal F(Z+4)/F(Z) telescoping does not terminate (old lane, confirmed).
- The companion's hypergeometric closed forms (Theorem 1.1 diagonal; 7.3 curve) do
  not evaluate off the diagonal: Gauss/Kummer summation needs a+b = c or z-arguments
  1/2, and the double sum reduces to Appell F₃, not Gauss, off the diagonal.
- Termwise (13)-content is bounded below by the law by a factor 2^m; no termwise
  route can prove the Law (this is now a theorem-level obstruction: Theorem 2 shows
  pure coefficients are slice coefficients, i.e. already cumulant objects).
- The filtration-closure worry about the source's three-term parameter relation was
  checked against small cases (m ≤ 30) — no counterexample surfaced, but no proof
  either; not pursued (time).

## 8. Provenance

See `provenance.json`. Scripts: `core.py` (pipeline), `structure.py`,
`extended_checks.py`, `decomposition.py` (Theorems 1–3 checks). All integers exact;
no floats anywhere in the verification path.
