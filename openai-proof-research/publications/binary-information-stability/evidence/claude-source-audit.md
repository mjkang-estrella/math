# Claude source audit — combined R020 + R022 (binary-information stability)

2026-10-13. Auditor: Claude Opus 5.5 (`claude-opus-5-5`), acting as the review sub-agent requested by the user. **This is an AI audit, not human peer review.** It used no subagents, made no commits, edited no indexes or manuscripts, and submitted nothing externally.

## Verdict

**PASS (mathematics) with REPAIR (manuscript dependency accounting).** No mathematical gap was found in the new deductions of R020 (I302/I304) or R022 (I325/I334/I335) under the stipulated pinned OpenAI theorems. A standalone manuscript must still pay several **proof-internal source facts** that are not theorem statements. It must also write out lemmas that the research records only sketch (items R1–R4 below). None of these items is a missing idea. Each has a short replacement argument or an exact source equation to cite.

**Combining R020 and R022 into one paper: recommended** (see §6).

## 1. Sources, versions, identities

- Upstream (stipulated): `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, `preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/build/{main.tex,sections/*.tex}`. All eight files were freshly fetched from pinned raw URLs and **read completely**. SHA256 values are in `../tmp/upstream/SHA256SUMS`, and they match the raw hashes recorded in the I303 literature record (main `ad04285e…`, scalar `03b64ba1…`, canonical `fc449aa1…`, capacity `f0a33b2c…`, reserve `2b4c8b10…`, thinning `c52291a2…`, upgrade `2c0d5677…`, flow `9065dd3b…`).
- Research pin `mjkang-estrella/math@d513e308d86a38004d78bab9b9e88532e92bf56c`:
  - The staged copy is under `/tmp/publication-r017-r022/`. All 92 manifest hashes were re-verified, with 0 mismatches.
  - Read in full: R020 and R022; I300 (`a00cd592…`); I302 (`1db6cef3…`); I304 (`c9a10e57…`); I325 (`cee88674…`); I334 (`4a733cd4…`, matching I325's record); I334 profile comparison; I335 (`70e9a758…`); I303 and I336 reviews and literature records.
  - Fetched from the pinned raw URLs into `../tmp/research/` (hashes in `SHA256SUMS`): I290 (`2057261d…`) and I295 (`70992530…`), both matching I302's frozen list; I301 analysis and review; I332 (`299f7e7d…`, matching I325's record); I128, I131, I313 and I321.
  - Read in full from that set: I301 analysis and I332.
- Upstream catalogue: family 119 contains only the sharp-contraction and Boolean Hellinger preprints. Neither states a stability theorem, so no duplicate corollary was found in the pinned corpus.

## 2. Upstream hypotheses actually used (checked against TeX)

| Label | Exact hypothesis | Use | Check |
|---|---|---|---|
| `main:soft` | every n≥0, u:Ω_n→[-1,1], ρ∈[-1,1] | Δ≥0 for every comparison field; y≤w | ✓ |
| `upgrade:production` | g interior-valued | R≥0 at positive time; P290 | ✓ positive-time interiority, flow.tex 14–17 |
| `main:energy-split` | interior g | induction for BP; P290 | ✓ |
| `capacity:onebit` | g=m+δX, \|m\|+\|δ\|<1 | (C) core surplus; R325 §6.1 | ✓ applied only to genuine one-bit fields |
| `canonical:priced`, `canonical:coverage` | −1<b<a<1, 0<e≤e_max | K(m,d,e); uniqueness used in J290 | ✓ child entropies are positive, so means are interior |
| `reserve:joining` | e_a,e_b>0 | reserve branch of BP and J290 | ✓ |
| `thinning:payment`, `thinning:high-value`, `thinning:window` | x_c≥0, 0<λ≤1 | (T); J290 | ✓ |
| `upgrade:high-information`, `wall:monotonicity`, `upgrade:joining` | stated ranges | I334 §2, §4 | ✓ |

## 3. Audit of the new deductions

### R022 / I325 / I334

- **Modal bridge (2.8).** I checked b≤a: conditional Jensen, then J(m,·) is even and convex in m because ψ'' is convex. I also checked the exact identity d_a=B+(a−b)², and B≤d_a≤(1+2U_{a1})B, where the Bregman linear term cancels at bX_i. Var≤2I holds.
- **Spike-tolerant entrance (E325).** The comparison is clipping of L only, at fixed η0. The tangent inequality at I(u) needs no ordering, because f_r is concave (tV'/V=sinh2v/2v increases). The linear term is ≤Ca²√H+E_a, using orthogonality of degree-1 against degree-≥2 and E[C(L)W]=E[(C(L)−L)W]. The bad support keeps (k/2)‖Z‖² from ψ''≥1. Its output is controlled through ‖T_rZ‖≤P^θ‖Z‖. The leakage Π_{≤1}G=Π_{≤1}t−Π_{≤1}Z is controlled through (2.6), and the remainder through ‖T_re‖_p≤‖e‖₂ with p≤1+r1^{−2}. ✓
- **Quartic passage (N325).** I re-derived every term:
  - input: Eψ(m+C(L)) through order 4 (odd moments vanish), V(v) through order 2, and the good-set Bregman with the multiplier split at |L|≤a^{1/2};
  - output: T_rC(L) is odd, and E[L²Z] and E[L²T_rZ] are o(a⁴);
  - level-two square completion.

  The coefficient algebra and lower bound are **checked symbolically**: bracket=κm²/(3h)+(1−κ)/6≥(m²+1−κ)/12, EL⁴=3s⁴−2Σc_i⁴, and ψ(ra)−r²ψ(a)=−r²(1−r²)a⁴/12+O(a⁶). The bad entropy A_bad is retained as an exact nonnegative term. ✓
- **Relative cone (R325).** The decomposition (6.2) is exact: the v→A linear terms vanish by independence and symmetry, and the means agree. Further checks:
  - **Q11 checked symbolically**, including the value 2r²(1−r²)/3 at m=0, b=a.
  - Spikes in W are paid at order H with coefficient k/2−r⁴/(2(1−γ²))>0 when γ²<1−r1².
  - The coupling bound K0√H holds by the conditional-orthogonality cancellations I re-derived. K0²≤C(μ²+ε²)a²L0² is absorbable.
  - Clipping errors are relative: E_L/(a²L0²)→0, and they vanish at L0=0.
  - The one-bit bias term was checked symbolically: hF(J/h)−F(J)≥(2/3)m²J²/h.
- **Join G325.** The contradiction uses the absolute o(a⁴) only to enter the cone; the payment is relative. The quantifiers are correct. ✓
- **BP / I334 (uniform biased production).**
  - G is jointly convex: det Hess=2cI²(F''−6cm²), **checked symbolically**.
  - B_m≥G for I≥L/2.
  - (T) integrates (Δ/λ)'≥δ0 d_c²/8 using κ≥λ²d_c²/8 (p≤2).
  - (C) uses the perspective of a convex R with R(0)=0.
  - Flag chain rule: I=λJ_c+E_λ, and J≤λJ_c because the flag is independent of X.
  - E_λ≤(3/4)λσ_c log(1/λ), from g''∈[−2,−1].
  - The posterior identity bound gives J_c²≤L²d_c².
  - (Q) uses x=x_c+(1−λ)σ_c≤x_c+(1−λ).
  - The reflected-wall derivative ≥2(η−c)W0J holds via the source entropy ratio.
  - The case split, pooling at the original child states, d=0, base case and induction are all correct. ✓
- **Semigroup endpoint passage.** z'=R−Az with 2≤A≤K, z(0)=0, and positive-time interiority. The two-case lower bound is c m²r0⁴a⁴(1−r1^K)/(16K). Both alternatives are uniform as |m|→1, and d_a≤Eu²+a²≤2. The final split (|m|≥1/2 → BP; |m|≤1/2 and a≤a_* → G325; [a_*,a1] → R020) covers every case. ✓
- **Sharpness.** b(a)²=ha²−(2/3)m²a⁴+O(a⁶) and Δ=r²(1−r²)m²a⁴/(3h)+O(a⁶) are **checked symbolically**.

### R020 / I302 / I304 (and the earlier dependencies I128/I131/I290/I295/I300/I301)

- **Integrating-factor budgets (P128) and E128/E131.** Re-derived. ✓
- **Q131b compression.**
  - Values are preserved fiberwise.
  - The other singletons are preserved.
  - f_B'≥r²q gives gain ≥(r²/2)E(D₊²−D²).
  - ED₊²−ED²≥(1−r²)(c²−b_i²)−r²(M−c²), using Ed²≤M.
  - d_a(u)−d_a(g)≤4(c²−b_i²) when c≥a/2.

  ✓
- **L131.**
  - The Hessian blocks are q (nonconstant) and a²q (constant).
  - q>0 ⇔ (1−t²)V(t)/t is decreasing; **numerically checked** over (0,1)² down to ~5e−8 near the corners, and proved analytically in I304.
  - The Bregman identity G=kEBψ_in−EBψ_out+(1−k)ψ(m) was re-derived. ✓
- **J290/M290/P290/B290.**
  - The retained-loss composition (c0/8)δ_c²[kπ₊+k²π₋]/(k+π₊)≥(c0/8)(1−k)δ² was re-derived.
  - Equality forces k=1, the deterministic core and m_c=0. W(core)<c(core) strictly for m_c≠0, since c_m>0.
  - Uniqueness transfers to the law.
  - The strict-F branch is strict by the thinning slack, and by strict convexity at λ=1.
  - Compactness: Jjoin is lower semicontinuous once a uniform positive child entropy and an interior mean are extracted on the compact set.
  - B290 time selection and E131 re-entry are correct. ✓
- **U300 (Gaussian strictness).** I re-derived:
  - the Euler equation;
  - σ²E[(Qw')²/(1−h²)]=kD (both factors of σ);
  - the second variation G''=f''A²+kD−E[(Qw')²/(1−h²)]+(1−k)m'²/(1−m²), with cancellation of the w'' terms;
  - the Cauchy–Schwarz bound m'²≤D(1−m²)(1−q);
  - E_prod R²=1+q, hence q≥b.

  The strict inequality (S) is **numerically checked** on a 59×59 grid including a=1−10⁻⁶: min of the normalized gap is 1.5e−6>0. The analytic proof via K(a)>0 and coefficient-ratio monotonicity is read and correct. The regularity in I301 §5–7 (Gaussian lower bounds for 1±w, the Fisher bound, linear growth of (V(w))') is adequate. Smoothing removal via f_s∘f_τ=f_σ is correct. ✓
- **G302 and diffuse transfer.**
  - Borell, layer cake and convex order are correct.
  - Helly compactness and joint continuity in (w,σ) are correct.
  - Influences of monotone kernels satisfy ≤ĥ(i).
  - The MOO fixed-degree replacement is correct.
  - The clipping projection inequality ‖Q_σv−clip(q)‖≤‖v−p‖ holds.
  - The error order is correct: η_G first, then d, then k.
  - Using λ∈(r1,1) removes any r1·a1 restriction. ✓
- **R020 sharpness.** K(a,r)=q(a,r)/2 is **checked symbolically**.

## 4. Numerical sanity checks of source proof-internal margins (not proofs)

These are in `../tmp/checks/numeric_checks.{py,out}` (mpmath, 30 digits, seed 20261013).

| Check | Result |
|---|---|
| N3: thinning margin λΔ'−Δ≥(2−3M)κ | min excess/κ=0.639 |
| N6: reserve corner margin A·W'−W≥(2−3M)κ | min excess/κ=0.454 |
| N2: η=2−max_{[0,L/2]}F''/F' | 0.2295 |
| N2: Ξ(L/2) | 0.01679 |
| N2: I334 constant c=δ0/(16C0) | ≈1.650×10⁻³ (binding term B0/C0) |
| N4: (GCP) with this c | minimum relative slack 0.0051≥0; empirical admissible c up to ≈0.89 |
| N5: reflected-wall derivative/(W0J) | min 1.036 (claimed bound 0.456) |
| N7: (D−F(I))/(m²I²) on 1500 random interior fields, n≤4 | min 2.67≫c |

Symbolic checks: 18/18 pass (`../tmp/checks/symbolic_checks*.{py,out}`). Two first-pass "FAIL" lines were only sympy's failure to simplify atanh against log; they re-pass after rewriting atanh as a log.

## 5. Unpaid items for a standalone manuscript (REPAIR list)

**R1. Proof-internal source facts used as if stated.** The research records call these "actual displayed source facts". They are not theorem statements, so under the stipulation boundary (theorem statements only) the manuscript must re-prove them or cite them as source-proof equations. Precise locations and replacements:

| Fact | Source location | Used in | Replacement |
|---|---|---|---|
| (a) λΔ'−Δ≥(2−3M)κ | `thinning.tex` 124–143 plus Lemma `thinning:window` (proof of Thm `thinning:payment`, 430–440) | I334 (T); J290 | Cite eq. `thinning:normalized-derivative` and Lemma `thinning:window`. The combination is two lines, and the identity is an exact calculus identity (also numerically confirmed). Prefer reproducing the identity's derivation in an appendix. |
| (b) A dW/dA−W≥(2−3M)κ | `reserve.tex` 181–197 (proof of Lemma `reserve:corner`) | J290 strict retained loss | Same treatment: cite `reserve:euler`, `reserve:intercept-bound` and the stated Lemma `reserve:geometry`. |
| (c) F''/F'<2 on [0,L/2] (`wall:rate-slope`) | `upgrade.tex` 113–128 | I334 η | Rederive from the *stated* Lemma `scalar:scaled-curvature` (three lines, as in the source). Alternatively state η as max over a compact set of a continuous function <2. |
| (d) Q0/V(m)≥exp(2J) (`wall:entropy-ratio`) | `upgrade.tex` 140–155 | I334 §4 | Re-derived here: ∂_d{log(A/V(m))−2J}=[G(v₊)−G(v₋)]/(v₊+v₋), with G(v)=cosh²v−v². Include it. |
| (e) Ξ(L/2)>0 and B_m−F≥m²Ξ(I) for I≥L/2 | proof of `upgrade:high-information`, 33–90 | I334 §2 | The tangent argument was re-derived here (c_m≤m²k0 from ψ≥m²/2). Include it, with Ξ(L/2)>0 from the stated Lemma `scalar:curvature-growth` plus the exponential balance. |
| (f) Posterior identity J=(p/2)ψ(d/p)+(σ/2)ψ(d/σ), giving J_c≤Ld_c²/(σ_c(1+x_c)) | `thinning.tex` 393–399 | I334 (10.7) | One-line expansion; include it. |
| (g) Two-geometry classification of the canonical optimizer, and the transition e₀ | `canonical.tex` 235–291 (prose, not a numbered result) | I334 §§3–4; J290; BP | Either restate it as a lemma with that proof, or cite it explicitly as used inside the stated Thm `upgrade:joining`. |
| (h) Flag chain rule I=I(U;X,B), J=I(U;X) | `thinning.tex` 58–72 | I334 (10.5) | Elementary; restate it. |

Also: I334 uses F''≥μ=1/(2L²). The *stated* Lemma `scalar:profile-convexity` gives F''≥4/3>μ. Using it is cleaner and only enlarges admissible constants.

**R2. Earlier internal lemmas written only at sketch level in I304.** L131 (spike-tolerant local coercivity with explicit p_*, ε_*), M290 (lower semicontinuity and compactness with endpoint exclusion), the MOO transfer with the unbounded dist² test (mollification order τ→0 after k→∞), and Borell convex order all need full proofs or precise citations:
- MOO: Annals 171 (2010), Hypothesis 4 and Thm 3.18.
- Borell (1985), or Mossel–Neeman arXiv:1210.4126.
- Bonami–Beckner for real-valued hypercontractivity (the two-point proof in I304 lines 121–126 suffices).

I301 §§2,5–7 is already at manuscript level for U300.

**R3. Constants.** BP's constant is explicit: c=(2−4L²)/(16(4L²+3L/2))≈1.65×10⁻³. Say so instead of "absolute c". Stability constants C stay existential, from contradiction and compactness, and the manuscript must say this.

**R4. Notation collisions to fix in the manuscript.** Several symbols carry multiple meanings across the chain:
- `J` is used for information increment, for the upstream joining surplus, and for J(m,b);
- `A` is used for the secant slope, for log(2/(1+x)), and for the clipped base;
- `B` is used for the modal residual and for the profile B_m;
- `K` is used for the max of F', for the canonical cost, and for K(a);
- `H` is used for Walsh higher energy and for binary entropy;
- `M` is used for 4L²/3 and for Eu².

None of these collisions causes an error in the records, but a single manuscript must disambiguate them.

No BLOCK item was found.

## 6. Combining R020 and R022 as one paper

**Recommended.** The headline theorem can be R022's statement: d_a≤C(a1,r0,r1)a^{−4}[ψ(ra)−I(T_ru)] for all 0<a≤a1. At fixed a0 this contains R020's linear bound, with an a0⁻⁴ loss that is absorbed into C. R022 genuinely uses R020 as its compact-amplitude component; it is not separable without restating R020. The two also share:
- the integrating-factor budget;
- the Bregman, hypercontractive and support spike payment;
- the modal bridge and the noise-time positive interiority.

Suggested structure:
- **Theorem A:** compact-amplitude linear stability, with sharp exponent 1.
- **Theorem B:** the small-information a⁻⁴ endpoint, with sharp exponent 4.
- **Theorem C:** uniform biased production BP.
- Sections: the Gaussian strictness and rearrangement part (U300/G302/transfer); the cube marked-sector part (J290–B290, L131, Q131b); and the endpoint part (E325/N325/R325/BP).

Attribution in the paper should keep R020 and R022 distinguishable: they are two separately accepted findings, each with its own contribution boundary. The paper must credit the upstream theorems and source-proof equations (R1) explicitly.

## 7. Literature boundary (spot-checked 2026-10-13)

- Ky–Tran arXiv:2609.31797 v1 (25 Sep 2026; only version listed) is stability for **Boolean** f relative to the dictator. It gives no soft-kernel or small-information rate statement (abstract checked).
- Chen et al. arXiv:2609.24931 v2 §9 is credited for arbitrary-array production. Its displayed hybrid profile equals F(I) on a small-information interval at some fixed mean; this is I334's profile comparison, whose algebra I335 re-derived. That defeats evaluation of the displayed profile, but does not prove novelty.
- Heilman–Tarter (translations), MOO, Borell and Mossel–Neeman, and Bonami–Beckner are credited classical or predecessor tools.
- A web search on 2026-10-13 found no soft or biased stability result superseding R020/R022 (search results included 2601.09679, 2609.24184, 2609.28534, 2610.10618).

The search was not exhaustive, and no worldwide priority is claimed.

## 8. Not inspected

- Upstream proof truth (stipulated).
- Lemma `thinning:interval` internals.
- Full bodies of I290, I295, I131, I128, I313 and I321. They were fetched and hash-checked, but only the parts restated in I304, I325 and I335 were audited.
- I303/I336 analysis bodies beyond their reviews and literature records.
- The Hellinger companion.
- Full external papers: Ky–Tran (abstract only), Chen et al., MOO, Borell.
- Any formal or Lean verification.

Numerical checks are sanity evidence, not proof.
