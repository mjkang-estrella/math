# Preliminary adversarial review — root-gaunt-integral-r16 (Gaunt Conjecture 2.4, MathDB 339406)

Reviewer: pi GLM-5.3-Flash, thinking=high, SOLO preliminary review, 28 October 2026.
Credit 0 maintained. No acceptance or counting performed; root adjudicates.
No git/shared/lane edits, no children, no external messages. Independent scripts ran under
`ulimit -v 524288`, single process, no pools (scripts in `scripts/` of this lane).

## 1. Verdict summary

**Recommend: advance to a full/final review.** The ordinary proof was verified correct by
independent symbolic and numerical means; source fidelity is confirmed against the actual
arXiv v2 PDF (printed p. 7 visually read); the mandatory SUBSUMPTION gate found **no named
primary theorem that subsumes the result**, and I additionally established a concrete
separation showing the proof mechanism (convexity in *squared* order) is not a routine
corollary of the classical convexity in the order itself. The recurring objection (possibly
known folklore squared-order convexity; unpublished-body clearance; incomplete formal
endpoint) remains open and is accurately stated by the candidate.

## 2. Freeze verification

All 27 paths of `review-freeze.json` verified against SHA-256 before review: **27/27 OK**
(re-verified after review, unchanged; see §9). The frozen `PROOF.md`, `SOURCE-PRIOR.md`,
`checks.py/json`, `retrievals.json`, `provenance.json` and all 21 source files were read.

## 3. Source fidelity

- `sources/conjecture-page.png` (rendered printed p. 7) visually read by me: Conjecture 2.4
  states exactly n<1; α_ν,n := ν+n−√((ν+n)²−2ν−1) for ν ≥ 1−n+√(2(1−n)); (2.17)
  ∫_x^∞ K_{ν+n}(t)/t^ν dt > K_{ν+n−α}(x)/x^ν for all x>0; equality at n=1 for all ν∈ℝ;
  optimality disjunction for β ∉ {α, α′}; Remark 2.5 with the unproved derivative
  comparison (2.18) marked "(?)", and the explicit admission that the integer-β Appendix A
  proof "cannot be easily adapted".
- Candidate's translation is exact: μ=ν+n, δ=√(μ²−2ν−1), so ν+n−α_ν,n = δ and
  ν+n−α′_ν,n = −δ (K even). The candidate's derivative inequality (3) is *literally* the
  source's (2.18): I expanded the source's displayed form
  −[(ν+δ)K_{δ+1}+(δ−ν)K_{δ−1}]/(2δx^ν) via the recurrence and it equals
  −x^{−ν}[K_{δ−1}+(ν+δ)K_δ/x]. ✓
- The source threshold is exactly δ²≥0: at ν=1−n+√(2(1−n)) the radicand (ν+n)²−2ν−1
  vanishes and its derivative 2(ν+n−1) ≥ 2√(2(1−n)) > 0 beyond. ✓
- MathDB 339406 record read (frozen): statement matches the PDF; status open/empty — used
  only as status, not novelty evidence. ✓
- I did **not** access the published Proc. AMS body (AMS VoR/AM/viewer all 403 per frozen
  retrievals; Manchester record links only arXiv). Body clearance remains open, correctly.

## 4. Independent mathematical verification

### 4.1 Exact symbolic identities (sympy, `review_checks.py` "exact")
All four asserted identities expanded to identically zero: radicand shift
(μ−1)²−2(1−n)=μ²−2ν−1; order gap ν²−δ²=(1−n)(2ν+n+1)>0; chord coefficient
(c−a)/(b−a)=(ν+δ)/(2δ); sharpness coefficient (4μ²−1)/8−ν−1/2=(4δ²−1)/8. ✓

### 4.2 Proof step audit (all steps re-derived independently)
1. **Convexity**: λ↦cosh(u√λ) has entire series Σu^{2j}λ^j/(2j)! with positive
   coefficients; the j=2 term is strictly convex, so the sum is strictly convex on
   [0,∞) for u>0; integration against e^{−x cosh u} (a positive measure dominating every
   fixed exponential) preserves strict convexity. ✓
2. **Chord extrapolation** (δ>0): a=(δ−1)², b=(δ+1)², c=μ² with a<b<c (uses ν>δ, i.e.
   ν²−δ²=(1−n)(2ν+n+1)>0, and μ²−(δ+1)²=2(ν−δ)>0); strict convexity gives
   F(c) > F(a)+(c−a)/(b−a)(F(b)−F(a)); with K_{|δ−1|}=K_{δ−1} and the recurrence
   K_{δ+1}−K_{δ−1}=2δK_δ/x this yields (2). ✓
3. **Zero order**: tangent at λ=1: F(μ²)>F(1)+(μ²−1)F′(1) with μ²−1=2ν>0;
   F′(1)=½∫u sinh u e^{−x cosh u}du = K_0(x)/(2x) by IBP (boundary term u e^{−x cosh u}
   vanishes at 0 and ∞). Gives (2) at δ=0. ✓ The candidate correctly identifies that the
   source's divided display is singular at δ=0 and handles it separately.
4. **Derivative comparison**: d/dx[x^{−ν}K_δ] = −x^{−ν}[K_{δ−1}+(ν+δ)K_δ/x] (standard
   K′=−K_{δ−1}−δK_δ/x), so (2) gives (3)=(2.18). ✓
5. **Integration**: t^{−ν}K_μ(t) integrable on [x,∞) (exponential decay), boundary term
   t^{−ν}K_δ(t)→0; the integrand difference is strictly positive on all of [x,∞), so the
   integral inequality is strict. ✓
6. **Optimality sufficiency** |η|≤δ: K_η<K_δ for |η|<δ by cosh(ηu)<cosh(δu) on u>0;
   |η|=δ by evenness. **Necessity** |η|>δ: fixed-order large-x expansion of K_η and of the
   tail (Watson/IBP) gives difference ∼ √(π/2)e^{−x}x^{−ν−3/2}(δ²−η²)/2, negative for
   large x. ✓ (See 4.4 for numerical confirmation of the leading coefficient.)

No gap found. The argument is self-contained and does not silently assume any derivative
comparison, integer order, or n≥0.

### 4.3 Key adversarial analysis: is the mechanism *routine*?
The genuinely load-bearing step is convexity of λ↦K_{√λ}(x), not the classical convexity of
ν↦K_ν(x) (which is trivial from the same integral and effectively folklore). I checked
whether the classical tool alone suffices: convexity of ν↦K_ν(x) plus secant-slope
monotonicity yields K_μ > K_{δ−1} + ((μ−δ+1)/2)(K_{δ+1}−K_{δ−1}), i.e. coefficient
(μ−δ+1)/2 instead of the needed (ν+δ)/(2δ). The needed coefficient is ≤ the classical one
iff ν+δ² ≥ δμ. This **fails** on explicit admissible parameters, e.g.
(δ,ν)=(3,6),(2,5),(5,12),(1,3) (all admissible with n=μ−ν<1, verified). On that sub-family
the classical route is strictly too weak, while the conjecture inequality still holds
(verified numerically). **So the candidate's squared-order convexity is doing genuine,
non-substitutable work** — this materially weakens the "routine corollary" objection.

### 4.4 Independent numerics (`scripts/review_checks.py`, mpmath dps 30 + scipy scaled)
- **600** randomized admissible (n,ν,x) checks of the literal conjecture inequality AND the
  pointwise three-order comparison: 0 failures (n∈[−25,0.95), ν at and above threshold,
  x∈{0.02,0.7,1,7,60}; mpmath besselk + tail quadrature).
- **25** exact zero-order boundary cases (δ=0 exactly, e.g. (n,ν)=(0.5,1.5),(−1,4),
  (−3.5,7.5),(−8,9+√18)): conjecture and tangent comparison pass; 0 failures.
- **12** sharpness checks: for η=δ+1 the proposed bound fails at large x (found failing x
  in {30,...,240} in all cases); plus **4** scaled-float64 sharpness checks at x=300:
  difference negative in 4/4.
- **4** large-x main-inequality checks via independent e^x-scaled float64 integration
  (kve): 4/4 positive at x=300.
- **Asymptotic leading coefficient**: normalized difference
  (tail−x^{−ν}K_η)/S → (δ²−η²)/(2x) confirmed; relative deviations vanish like 1/x²
  (e.g. 28%→12%→6% at x=60/150/300 for the large-δ case), matching the O(x^{−2}) term;
  the exact 1/x coefficient (4δ²−1)/8 verified symbolically.
- All checks pass. **Reviewer pitfall worth recording**: mpmath's semi-infinite `quad`
  drifts on deep tails (x≥80) — two mpmath methods agreed with each other yet disagreed
  with a correctly e^x-scaled scipy computation, which matched theory. Root's own
  `checks.py` already used the scaled-kve approach and is unaffected; but any future
  diagnostics for the sharpness part should use scaled integrals.

## 5. Formal component (root-gaunt-formal-r1 @ d8abf08d32)

`IntegralBase.lean` and `SquaredOrder.lean` read in full. They prove exactly what
SUMMARY.md claims: the literal Schläfli integrand, integrability by the explicit Gaussian
domination exp(|v|²/x)e^{−(x/4)u²}, strict convexity of the literal besselK in squared
order via a strict integral comparison on a set of positive measure, the closed three-order
inequality for d>0, and the kernel-level tangent at λ=1. No `sorry`-shaped substitutes seen
in source; pins specify Lean 4.34.1 / mathlib d13f23b, std3. I did not re-run the Lean
build (out of scope for this memory-capped preliminary pass); audit.json/Checks.log hashes
are in the component's own provenance and were not re-verified here.

**Remaining formal bridges (agreed, absent):** (i) recurrence/derivative of the integral
w.r.t. x (IBP + dominated differentiation); (ii) the zero-order identity
∫u sinh u e^{−x cosh u} = K_0/x; (iii) source parameter geometry, literal t^{−ν} tail
integrability, infinity limits, FTC to GauntConjecture2.4; (iv) if optimality is included,
genuine formal fixed-order asymptotics (currently absent entirely); (v) a named bridge from
the Schläfli definition to whatever definition the endpoint fixes. This is a substantial
endpoint, dominated by (iv). **Full FORMAL PASS is not claimable and I do not claim it.**

## 6. SUBSUMPTION screen (bounded; per gate, mandatory)

Named primary sources checked (body level unless noted):
1. **Yang–Tian 2022** (Rev. Mat. Complut., PMC9361280; root-read, I re-read the abstract
   and theorem scope): resolves Gaunt's *different* Open Problem 2.12 (ratio W_ν
   convexity, first kind). Not Conjecture 2.4.
2. **Yang–Tian 2019** (arXiv:1803.02513/JMAA): fixed-order argument monotonicity of
   x+xK′_ν/K_ν; no all-real three-order extrapolation.
3. **Mao–Tian 2023** (C. R. Math. 361, crmath.399; root body-read): Turán defects
   T_{ν,α,β}=K_ν²−βK_{ν−α}K_{ν+α}, absolutely monotonic *in ν*; different objects; no
   squared-order convexity of K and no linear three-order bound.
4. **Yang–Zhang 2026** (arXiv:2605.20983, the only 2026 citer; abstract read live via
   arXiv, 28 Oct 2026): "affirmative full-range solution to Gaunt's 2019 Open Problem
   2.10" — first-kind ∫₀^x endpoint majorants. **Different problem; no subsumption.** ✓
5. **Baricz–Ponnusamy 2013** (Proc. AMS, arXiv:1010.3346): Turán inequalities;
   log-convexity of the *product* I_{√ν}K_{√ν} in order — different function; also the
   subject of a trureturing Blueprint counterexample page (product not log-convex in
   order) — unrelated to our convexity claim.
6. **DLMF §10.37** and classical monotonicity tables: no squared-order convexity recorded.
7. **trureturing registry**: searched live (mdbook Library + Blueprint); only
   BesselProductOrderLogConvexity pages; no hit for 1806.00524 or squared-order convexity
   of K. Consistent with root's earlier grep.
8. **All 14 Semantic Scholar citation records** of 1806.00524 enumerated live
   (28 Oct 2026): Struve/Lommel/variance-gamma/Horn/2025-Lommel-ratio plus the above;
   none titled or abstracted as a resolution of Conjecture 2.4; only Mao–Tian and the four
   above were body/abstract-assessed in depth — the remaining titles were screened only.
9. **Gaunt follow-ups**: 2501.12197 (2025) concerns ∫₀^x e^{−γt}t^ν I_ν — first kind,
   different integral.

**No published squared-order convexity of K_ν(x), absolute monotonicity in ν², or general
three-order linear inequality implying (2) was found.** Combined with §4.3 (classical
order-convexity provably insufficient on an explicit admissible sub-family), the
routine-corollary objection does not stand on the evidence gathered. This is a bounded
screen, not novelty clearance: MathSciNet/zbMATH untouched, the published AMS body
unread, and negative search results are weak evidence.

## 7. Strongest remaining objection and falsifier

**Objection:** the entire proof is a short exercise on the classical Schläfli integral; the
specific observation "K_ν(x) has positive Taylor coefficients in ν², hence is convex in
ν²" may exist as folklore or an unpublished remark (it is a two-line observation), and any
future or obscure publication of it would reduce the candidate to a routine corollary.
The published-body comparison is also open (AMS 403s).

**Falsifier:** a named primary theorem stating convexity (or absolute monotonicity) of
λ↦K_{√λ}(x) for fixed x>0, or any published three-order inequality implying
K_μ > K_{δ−1}+(ν+δ)K_δ/x under μ²=δ²+2ν+1 (or the source's (2.18)); or a published
resolution of Conjecture 2.4. A single such source with a complete bridge excludes the
candidate's novelty claim. Conversely, a falsifier of the *mathematics* would be an
admissible (n,ν) with the inequality failing — my 600-case sweep and 4 scaled large-x
checks found none, and the analytic proof has no gap I could find.

## 8. Remaining work before any acceptance decision

1. Published-body access ( lawful route only; respect 403/challenge controls) and
   comparison of the journal Conjecture 2.4 with arXiv v2.
2. Broader prior sweep (MathSciNet/zbMATH if available; "convex in the square of the
   order" phrasings; author follow-up bodies, especially any Gaunt paper citing 2.4).
3. Full formal endpoint per §5 (the asymptotic/sharpness part is the expensive item;
   decide scope before investment).
4. Manuscript + packet + fresh replay per campaign rules.
5. Optional: a short remark strengthening the case — record the §4.3 separation
   (classical order-convexity insufficient for ν+δ²<δμ) in the paper.

## 9. Post-review freeze re-verification

All 27 frozen hashes re-verified after review: **27/27 unchanged** (see provenance.json).

No credit recommendation is made; root adjudicates.
