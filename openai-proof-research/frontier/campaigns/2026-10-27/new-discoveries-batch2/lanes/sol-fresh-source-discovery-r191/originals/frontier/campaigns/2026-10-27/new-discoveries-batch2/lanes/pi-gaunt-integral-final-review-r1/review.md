# Integrated independent FINAL review — root-gaunt-optimality-r3 @ c20af1d79a

Reviewer: pi GLM-5.3-Flash, thinking=high, SOLO adversarial final review, 28 October 2026.
Scope: the complete 80-declaration / 14-module iff endpoint, manuscript, packet and sources of
`lanes/root-gaunt-optimality-r3` at commit c20af1d79a. Credit 0 maintained throughout; **no
acceptance, no counting, no public action** — root alone accepts. No children, no git writes,
no shared/other-lane writes, no external messages. All my scripts ran under `ulimit -v 524288`,
single process, no pools.

I read the preliminary review (pi-gaunt-integral-preliminary-review-r1/review.md) and the
adoption note (root-gaunt-optimality-r3-review-adoption.md) but adjudicated independently and
at full strength; I do **not** inherit the parent's extracted-audit PASS — I re-derived it.

## 0. Freeze and packet verification (all independent, from my OWN copies)

- All **80** non-prebuilt files of the lane hash-verified against `final-review-hashes.json`:
  **80/80 OK, zero mismatches, zero missing** (before and after review; originals untouched).
- `packet/gaunt-optimal-tail-proof.zip` SHA-256
  `053334f3dc7aae1bd22c97a603c66b7b5f5f9ca8bd9ba759a3fbb3b5733ce95e` (matches task and receipt);
  copied to my lane (`own-copy/`), freshly unzipped: **71 entries = 70 payload + MANIFEST.json**;
  MANIFEST SHA `07c73362dccd2e77aae1492f56d491ee6e69b9874fbb65e39c1fdf4907bdb39f`; **all 70
  payload hashes verified against the manifest**; the manifest's payload set contains **no
  .olean/.so/.ilean/trace or any prebuilt candidate artifact** (lane `formal/*.olean` are
  excluded from the packet).
- Pinned toolchain asserted by the replay itself: Lean binary at
  `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`,
  SHA `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`, version string
  `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`;
  all **8 package revisions** (LeanSearchClient, Qq, aesop, batteries, importGraph, mathlib,
  plausible, proofwidgets) `git rev-parse HEAD`-verified **and clean-tree verified**.

## 1. Gate 1 — FRESH STRICT SOURCE REPLAY: **PASS**

I ran `python3 verify_candidate.py` from **my own extraction** (`extracted-fresh/`), not from
the lane's build tree. Result: **PASS 14 modules / 80 declarations** in 45 s wall time.

- All **14 module logs empty** (0 bytes each) under `-DwarningAsError=true`.
- `Checks.lean` audits exactly the 80 regex-counted declarations (`checked == declared`,
  verified programmatically; no `@[...]`-attributed, instance, abbrev, example, opaque or
  private declarations escape the count — grepped, none exist in the sources).
- **All 80 axiom reports read**: every one is exactly `[propext, Classical.choice, Quot.sound]`;
  grep for any other axiom line and for `sorry|admit|Ax` over the log: **no hits**.
- Endpoint present: `GauntIntegral.source_full_classification_339406 : SourceClaim339406Full`.
- My fresh `verification/audit.json` and `verification/Checks.log` are **byte-identical** to the
  lane's (audit `c7c83be1…`, Checks `efe7eb6d…`), i.e. the frozen artifacts are exactly what a
  clean replay produces. I did not inherit the parent's PASS; I reproduced it.

## 2. Gate 2 — FORMAL/MATHEMATICAL CONTENT: **PASS**

I read all 14 Lean sources in full and re-derived every load-bearing identity by hand:

- **K is the actual function.** `besselK v x = ∫_(u>0) e^(−x cosh u) cosh(v u) du`, exactly
  DLMF 10.32.9 (archived body read; |ph z|<π/2 covers real x>0). Grep confirms **no reference to
  any Mathlib Bessel definition anywhere in `formal/`** — no surrogate K, no silent equational
  bridge. Evenness, positivity, integrability (explicit Gaussian domination
  `cosh(ρu) ≤ e^{|ρ||u|}`, `|ρ||u| ≤ x u²/4 + ρ²/x`) are all proved from the integral.
- **Squared-order convexity** (`IntegralBase`/`SquaredOrder`): a ↦ cosh(u√a) = Σ u^{2k}a^k/(2k)!
  is a sum of convex terms with a strictly convex k=2 term for u≠0; `Summable.tsum_lt_tsum`
  lifts pointwise strict convexity to `K_{√a}(x)` strictly convex on [0,∞). Sound.
- **Chord extrapolation** (δ>0): strict convexity on (δ−1)² < (δ+1)² < δ²+2ν+1 gives
  (ν+δ)K_{δ+1} + (δ−ν)K_{δ−1} < 2δK_μ; I re-checked the coefficients
  (δ²+2ν+1−(δ+1)²)/(2(ν+δ)) = (ν−δ)/(ν+δ), 2δ/(ν+δ). Sound; uses only ν>δ from the parameter
  geometry ((ν²−δ²) = (1−n)(2ν+n+1) > 0, proved in `source_parameter_geometry`).
- **Zero order** (`ZeroOrder`): genuine IBP identity ∫ u sinh u e^{−x cosh u} du = K_0(x)/x
  (boundary term t e^{−x cosh t} → 0 at both ends) plus the strict tangent of cosh(u√λ) at
  λ=1 gives K_1 + (ν/x)K_0 < K_μ at μ²=2ν+1; K_{−1}=K_1 handles δ=0. No division by δ. Sound.
- **Recurrence and argument derivative** (`Recurrence`/`ArgumentDerivative`): both IBPs are
  genuine (boundary terms vanish via exponential domination); K'_ν = −(K_{ν+1}+K_{ν−1})/2 via
  dominated differentiation with an x/2-neighborhood domination; lower form
  K'_ν = −K_{ν−1} − (ν/x)K_ν. Sound.
- **Weighted tail calculus** (`TailBounds`/`WeightedComparison`): d/dt[t^{−ν}K_d] =
  −t^{−ν}K_{d−1} − (ν+d)t^{−ν−1}K_d; the weighted FTC integral
  ∫_x^∞(−weightedK v (d−1) − (ν+d)·weightedK (v+1) d) = −weightedK v d x is correct, with
  integrability from the explicit exponential bound K_ρ(t) ≤ e^{−t/2}K_ρ(a/2) for t ≥ a > 0
  and limit 0 at ∞. Every quantifier and domination I inspected is the real one.
- **Optimality route is the NEW local kernel, not the historical asymptotics.** No fixed-order
  asymptotic theorem appears anywhere in the 14 modules. The route is exactly OPTIMALITY-ROUTE.md:
  for r > δ, h(u) = cosh(μu) − A cosh((r+1)u) − B cosh((r−1)u), A=(ν+r)/(2r), B=(r−ν)/(2r);
  h(0)=h′(0)=0, h″(0)=δ²−r²<0 (I recomputed: the exact jet is
  [(ν+r)(r+1)²+(r−ν)(r−1)²]/(2r) = r²+2ν+1, so h″(0)=μ²−(r²+2ν+1)=δ²−r²). Two MVTs
  (`negative_near_zero_of_second_derivative`) give h<0 on (0,ε]; the window [a,b]⊂(0,ε) with
  max −c plus the global tail envelope T·C, T=e^{−(x−1)cosh ε}, C=∫e^{−cosh u}|h| — I checked
  all three regions of `laplace_eventually_negative` pointwise (window, (0,ε]∖[a,b], (ε,∞)),
  the identity T = e^{cosh ε}e^{−(cosh ε−cosh b)x}e^{−x cosh b}, and the final nlinarith.
  The recurrence identifies D(x)=K_μ−K_{r−1}−(ν+r)K_r/x (I verified the A·K_{r+1} rewrite:
  coefficient of K_{r−1} is (ν+r)/(2r)+(r−ν)/(2r)=1). Weighted FTC then gives
  ∫_x^∞ t^{−ν}K_μ − x^{−ν}K_r = ∫_x^∞ t^{−ν}D(t)dt < 0 for **every** x beyond the threshold
  (strict via positive-measure support on (x+1,x+2)), i.e. the bound fails eventually for every
  |r|>δ. The iff is closed by cosh-monotonicity in |order| (`besselK_le_of_abs_le`).
- The endpoint type is literally the task's LITERAL FULL CLAIM: all real n<1, ν ≥
  1−n+√(2(1−n)), δ=√((ν+n)²−2ν−1), all real r, all x>0, iff |r|≤δ, plus the eventual strict
  converse; no residual analytic/frame/asymptotic/existence premise.

**Independent numerics** (`scripts/review_checks.py`, sha
`cd87629a3142af22a2bc0754bf0d5b66894414fea579e79177ff669d8fa7301b`, mpmath dps 25–40):
- 270 lower-bound checks (r=δ, r=δ/2, r=−δ; 18 admissible (n,ν) incl. n=−20, −5, 0.9, exact
  threshold; x ∈ {0.05, 0.7, 1, 4, 20}): **0 failures**.
- 36 zero-order boundary comparisons: **0 failures**.
- 54 eventual-negativity cases for r>δ: **0 genuine failures**. One case
  (n=−20, ν at exact threshold, r=δ+0.3) has an enormous threshold — D/K_r is still +1.2e−5 at
  x=4000 and turns negative by x=5·10⁴ (verified −7.9e−21724 at 5·10⁴). This is a diagnostic
  caveat about *explicit thresholds*, not a counterexample: the theorem claims only
  "sufficiently large".
- **New asymptotic cross-check**: D(x) = −s(s/2+δ)·√(π/2)·e^{−x}x^{−3/2}·(1+O(1/x)) for r=δ+s
  (derived from the K_ρ expansion with the correct sign (4ρ²−1)/8x); numerically confirmed to
  ~1% at x=500–8000 on four (δ,ν,s) triples. This also independently confirms the preliminary
  review's tail-defect coefficient (δ²−η²)/2 (since −s(s/2+δ) = −(η²−δ²)/2).

## 3. Gate 3 — SOURCE FIDELITY: **PASS on arXiv v2; journal-body comparison remains OPEN (HOLD)**

- Frozen `sources/gaunt-v2.pdf` (SHA `2334f3217556918ec1aba041d3dd8846246ffa91f0e510fdaecf6a57a2e4fcef`)
  text-extract and the rendered printed p.7 (`conjecture-page.png`) both visually read by me.
  Conjecture 2.4: n<1; α_{ν,n} := ν+n−√((ν+n)²−2ν−1) for ν ≥ 1−n+√(2(1−n)); (2.17)
  ∫_x^∞ K_{ν+n}(t)/t^ν dt > K_{ν+n−α}(x)/x^ν for all x>0; equality at n=1 for all ν∈ℝ;
  optimality: for β ∉ {α_{ν,n}, α′_{ν,n}}, either K_{ν+n−β}(x)/x^ν < K_{ν+n−α}(x)/x^ν for all
  x>0, or ∃y>0 with ∫_y^∞ < K_{ν+n−β}(y)/y^ν. Remark 2.5 records the unproved derivative
  comparison (2.18) marked "(?)" and admits the integer-β Appendix A proof "cannot be easily
  adapted".
- Mapping is exact: ν+n−α = δ, ν+n−α′ = −δ (K even), so (2.17) is the r=δ case of the endpoint;
  the candidate's iff **implies** the source's optimality disjunction (|r|<δ falls in the first
  alternative via pointwise K_r ≤ K_δ; |r|>δ gives the second, in the stronger
  every-sufficiently-large-x form). The candidate's comparison (2) is literally the source's
  (2.18) after the recurrence. n=1 is excluded on both sides.
- Frozen MathDB 339406 response read: same literal statement, `status: open`, used only as
  status, never as novelty evidence.
- **Live checks I performed (28 Oct 2026):** arxiv.org/abs/1806.00524 confirms only v1
  (1 Jun 2018) / v2 (9 Oct 2018), journal ref Proc. AMS 147 (2019) 2937–2951 — matching the
  frozen record. I could not lawfully reach the AMS VoR/AM body (frozen 403 challenge pages
  retained; Manchester record links only arXiv, per frozen `manchester-landing.html`). My
  attempts to resolve a live MathDB record URL returned 404 on guessed paths and no index hit.
- **Verdict**: statement-level fidelity to the actually-readable source (arXiv v2) is exact.
  Published-body clearance is **not claimed by me or by the packet** and remains the open
  source gate → this sub-gate stays **HOLD** as before. Metadata (OpenAlex "publishedVersion"
  label) correctly does not establish body equality.

## 4. Gate 4 — MANUSCRIPT: **PASS**

All three frozen rendered pages (`render/page-{1,2,3}.png`) visually read by me:

- Theorem 1 matches the Lean endpoint parameter-for-parameter (μ=ν+n, δ=√(μ²−2ν−1), iff,
  eventual strict converse, all real parameters; n=1 explicitly disclaimed). Formula-by-formula
  correspondence with the Lean statements checked: chord (3) = `besselK_three_order`;
  comparison (4) = `besselK_differential_comparison`; tangent = `orderKernel_tangent` /
  `besselK_zero_order_comparison`; K_0/x identity = `zeroTangent_integral`; derivative =
  `besselK_hasDerivAt_lower`; envelope (5) = `laplace_eventually_negative` with the same
  constants; D(x) identification = `comparisonKernel_integral`; final defect = `OptimalConverse`.
- `build/main.log`: zero Overfull/Underfull, zero LaTeX warnings, zero undefined references
  (grep clean; 3 pages output). paper-qa.json consistent.
- Attribution: Gaunt Conjecture 2.4/Remark 2.5, Proc. AMS 147 (2019) 2937–2951,
  DOI 10.1090/proc/14433, statement checked in arXiv:1806.00524v2; DLMF 10.32.9. Honest.
- Status language: "independent review pending" on the title page, explicit open
  journal-body/novelty gates, "zero discovery credit, carries no priority claim, does not
  change any public problem status". Honest. No stale historical notes found on the rendered
  pages; ORDINARY-PROOF.md is clearly marked historical/superseded in its header and is not
  load-bearing.

## 5. Gate 5 — NOVELTY / SUBSTANTIVE ELIGIBILITY: **HOLD (no named subsumer found; objection not cleared)**

My own bounded sweep today (fresh searches; nothing inherited):

- No published theorem stating convexity or absolute monotonicity of λ ↦ K_{√λ}(x), no
  squared-order convexity of K, and no published three-order K inequality implying the chord/
  comparison surfaced under: "convexity of K_nu in the square of the order", "K_{√λ} convex",
  Gaunt 1806.00524 resolution queries, "absolute monotonicity of K in order squared",
  three-order/cosh-kernel Laplace comparisons. Hits were the known adjacent literature:
  Yang–Tian 2022 (Open Problem 2.12, first kind), Yang–Tian 2019 (fixed-order argument
  monotonicity), Mao–Tian 2023 (Turán defects in the order), Baricz–Ponnusamy Turán,
  ratio/product convexity papers (PAMS 13522/15891, JMAA 2021), and the trureturing
  BesselProductOrderLogConvexity page (product, not K alone). Yang–Zhang 2605.20983 solves
  the different Open Problem 2.10 (first-kind endpoint majorants) — not miscredited here.
- All 10 OpenAlex citing titles re-read from the frozen citers file: none is a Conjecture 2.4
  resolution; consistent with the preliminary review's 14 Semantic Scholar records (title-level
  for most, body-level for the four key items).
- **Adjudication of the sign-corrected separation (review §4.3 as corrected by the adoption
  note):** needed = (ν+δ)/(2δ) ≤ classical = (μ−δ+1)/2 iff ν+δ² ≤ δμ; the concrete examples
  (δ,ν)=(3,6),(2,5),(5,12),(1,3) have ν+δ² > δμ (e.g. (3,6): 15 > 3√22≈14.07), so classical
  order-convexity is genuinely too weak there. I confirm the correction is right and the
  conclusion stands; note the final candidate does **not** rely on this separation at all — it
  proves squared-order convexity directly.
- **Strongest remaining objection (unchanged, decisive-if-true):** the two-line observation
  "K_ν(x) has positive Taylor coefficients in ν², hence is convex in ν²" may exist as folklore
  or in an unread body; combined with the (also classical) recurrence and weighted FTC it would
  make the endpoint a routine corollary. **Falsifier:** any named primary source stating
  convexity/absolute-monotonicity of λ↦K_{√λ}(x), or a published three-order inequality
  implying K_μ > K_{δ−1} + (ν+δ)K_δ/x at μ²=δ²+2ν+1, or a published resolution of Conjecture
  2.4 — with a complete bridge. None found; a bounded negative search does not certify absence.
  MathSciNet/zbMATH remain untouched; the published AMS body remains unread (also a novelty
  surface, since the journal body may contain remarks absent from arXiv v2).

## 6. Gate 6 — PACKET/PROVENANCE/DETERMINISM: **PASS**

Zip SHA, manifest SHA, 70/70 payload hashes, entry count 71, absence of prebuilt candidate
artifacts, pinned binary+packages, fresh replay byte-identity (§0–1) — all independently
reproduced. `checks.json` diagnostics (sympy exact identities = "0", 32 source-tail checks,
54 three-order checks, tangent checks) read and consistent; they are labeled diagnostics, not
proof. The "earlier eight modules byte-identical" claim verified against the 56-declaration
checkpoint lane `root-gaunt-integration-r2/formal` (8/8 IDENTICAL; my first comparison against
`root-gaunt-formal-r1` was the wrong baseline — recorded for honesty).

## 7. Verdict

| Gate | Verdict |
|---|---|
| Freeze + packet + deterministic provenance | **PASS** |
| Fresh strict source replay (own extraction) | **PASS** (14 modules / 80 declarations, std3, logs empty) |
| Formal/mathematical content (all 14 sources read; every identity re-derived; independent numerics + new asymptotic cross-check) | **PASS** |
| Source fidelity (arXiv v2 statement + optimality) | **PASS**; published AMS journal body comparison **OPEN → HOLD** |
| Manuscript (3 pages, no warnings, honest status) | **PASS** |
| Novelty / classical-subsumption / substantive eligibility | **HOLD** (no named subsumer found; folklore-convexity objection unresolved; no priority claimed) |

**What passes:** everything within my competence — the formal certificate, the mathematics, the
packet, and the manuscript are correct, faithful to the readable source, and honestly labeled.

**What remains HOLD (root owns the decision):**
1. Published Proc. AMS body access and comparison (lawful routes only; preserve HOLD while
   403-controlled; arXiv-v2 clearance must not be upgraded by metadata).
2. Substantive eligibility against possible prior squared-order convexity / absolute
   monotonicity / implying three-order inequality (broader sweep: MathSciNet, zbMATH, book
   literature, author follow-up bodies; the two-line-observation risk is irreducible by search
   alone).
3. Any acceptance, counting, or public action — none performed or recommended here.

Count unchanged: **accepted 2/30 additional, 32/60 total; all candidate credit 0.**

*Artifacts of this review (my lane only): `own-copy/gaunt-optimal-tail-proof.zip` (verified
copy), `extracted-fresh/` (own extraction + fresh replay outputs), `scripts/review_checks.py`
(memory-capped numerics). No file outside this lane was written; originals re-hashed after
review and unchanged.*
