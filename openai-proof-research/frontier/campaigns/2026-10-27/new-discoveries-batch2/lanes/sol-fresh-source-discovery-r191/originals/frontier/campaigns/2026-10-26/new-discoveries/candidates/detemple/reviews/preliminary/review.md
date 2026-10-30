# Preliminary adversarial review — DeTemple complete-monotonicity threshold (MathDB 328867)

Reviewer: pi-detemple-preliminary-review (solo, no children). Date: 2026-10-27.
Candidate: `../parent-detemple` frozen at commit `33bb01cb74` ("Freeze exact interior
DeTemple counterexample for independent review"), `preliminary-review-hashes.json`
plain25 SHA-256 map. Credit0; accepted tally 24/30 untouched by this review.

**Verdict summary**

| Gate | Verdict |
|---|---|
| Source | **PASS** — both statements read from actual primary bodies |
| Math | **PASS as preliminary argument** — every load-bearing bound independently rederived; one checker defect found (immaterial); no formal/Lean pass claimed |
| Novelty | **NO PRIOR RESOLUTION FOUND** (bounded screen; not a certification) |
| Substantive eligibility | **ELIGIBLE** — genuine positive strictly-interior failure, not endpoint/domain/typo, not an already-known corollary |

---

## 1. Source gate — PASS

All 25 frozen hashes verified before and after review; a byte copy was made under
`candidate-copy/` and re-hashed (all OK; the copy's `check_certificate.py` run
reproduces `certificate.json` byte-identically, confirmed by diff).

- **Preprint** Yang, arXiv:1409.6411v1 (16 pp, v1 only — checked live abs page;
  no revision/correction/withdrawal): Eq (3.3) p.12 reads
  G_a(x) = 24(x⁴+ax²+(7/40)a−31/336)R(x) − (x²−7/40+a) with R(x)=ψ(x+1/2)−ln x
  (Eq 1.10); Conjecture 1(ii) p.14: −G_a completely monotone on (0,∞) iff a ≤ 155/294.
  Both read directly from the stored text extraction.
- **Published** Yang–Chu–Zhang, J. Inequal. Appl. 2015:157, DOI 10.1186/s13660-015-0674-8:
  Eq (3.3) on publisher PDF **page 12** and Conjecture 1(ii) on **page 15** were
  visually read from the stored rendered page images (`published-p12.png`,
  `published-p15.png`); they match the preprint exactly. The font-mangled HTML
  extraction is consistent with the same fractions (7/40, 31/336, 155/294).
- **The published paper does NOT resolve the conjecture.** Its Corollary 1 /
  Remark 1 "positive answer to the conjecture (ii) posed by Chen" concerns Chen's
  separate conjecture on ((x+1)/x)²H(x) (its Theorem 1); Conjecture 1 is Yang's own,
  posed as open in §4 of both versions. The paper proves only the *necessity*
  direction a ≤ 155/294 (from −G_a = F_{−31/336} − a·f_{7/40} ≥ 0 and the x→0⁺
  ratio limit). The candidate refutes the *sufficiency* direction — no subsumption.
- **MathDB 328867** live refetch (`https://mathdb.com/api/posts/328867`, responseId
  mvqok2yljcd93s): byte-consistent with frozen `328867-live.json`; `status: open`,
  `lean_formalization_count: 0`, and **zero** solutions, replies, comments,
  model_attempts, human_solves, formulations.
- Theorem 4 of the source (G_a strictly CM iff a ≥ 11165/8284) concerns G_a, not
  −G_a; it does not decide the conjecture and is not subsumed by the witness.

## 2. Math gate — PASS as a preliminary argument

Independent re-derivation in `evidence/independent_check.py` (28/28 checks pass,
log in `evidence/independent_check.output.txt`; written from scratch, not derived
from the parent checker):

- Witness parameters: 155/294 − 527/1000 = 31/147000 > 0 (strictly interior),
  x = 1/50 > 0; P = 91379/525000000, P′ = 2639/125000, P″ = 2647/2500 — all exact,
  all positive.
- Log bounds re-derived from the atanh series: log 2 < 2/3+2/81+1/540 = 1123/1620
  < 7/10 (geometric tail bound re-derived), log 5 > 1924/1215, hence
  log 50 > 4658/1215 > 15/4. All confirmed numerically at 80 dps.
- ψ bounds: ψ(13/25) > ψ(1/2) = −γ−2ln2 > −31/15 (γ<2/3, ln2<7/10);
  ψ′ > 0; ψ″(13/25) = −2Σ(n+13/25)⁻³ ≥ −2·(8+∫₀^∞(t+1/2)⁻³dt) = −20 (integral
  comparison; actual sum ≈ 8.41 ≤ 10). Hence R > 101/60, R′ ≥ −50, R″ ≥ 2480 at
  x = 1/50. All pointwise bounds are in the correct direction for a *lower* bound
  on G″ (negative coefficients pair with upper bounds correctly: 48P′R′ ≥ −48P′·50).
- Exact assembly: 24·(2647/2500)(101/60) − 48·(2639/125000)·50 +
  24·(91379/525000000)·2480 − 2 = **510221/1093750** ≈ 0.46649 > 0, exactly as
  claimed. Hence (−G_a)″(1/50) < 0 and −G_{527/1000} is not completely monotone
  (CM ⇒ (−1)²f″ ≥ 0). The 70-digit mpmath value 14.3299153605…(70 digits)
  matches my independent mp.diff and symmetric-difference computations.
- Qualitative route at a₀ = 155/294 (7a₀/40 = 31/336 exactly): G″_{a₀}(x) → +∞ as
  x→0⁺ (numerically −2.35, 30.6, 85.5, 143.5 at x = 10⁻¹…10⁻⁴), and the
  finite-difference identity D(x)/x² = 24[(81x²+9a₀)h(3x) − 2(16x²+4a₀)h(2x) +
  (x²+a₀)h(x) − (50x²+2a₀)log x − (81x²+9a₀)log 3 + 2(16x²+4a₀)log 2] − 2 was
  verified **symbolically, residual exactly 0** (`evidence/fd_and_scope_probes.py`
  and review session log), with D(x)/x² → +∞ confirmed numerically (−2.7, 17.1,
  68.9 at 10⁻¹…10⁻³). The interior-a existence argument is sound: D_a(x) is
  affine in a at fixed x, and D_{a₀}(10⁻³) > 0, so some a < a₀ fails midpoint
  convexity at 2x. (Subtlety worth recording: the a₀ divergence does *not*
  persist in the x→0⁺ limit for a < a₀ — for a < a₀, D_a(x) → 24c·log(4/3) < 0
  with c = 7a/40−31/336, and the O(1/x²) negative term dominates. The interior
  failure for a < a₀ is existential at a fixed small x, which is all the proof
  needs; the FD route does **not** show failure for all a < a₀, and my probe of
  that stronger claim was refuted twice, analytically and numerically.)

### Objection M1 (checker defect — must fix before formalization; immaterial here)

`check_certificate.py` asserts a symbolic identity between `diff(g,x,2)` and `g2`
where **g omits the 24(7a/40−31/336)·R term** of source (3.3)
(`g = 24*(x⁴+a·x²)*(h−log x) − x² + 7/40 − a`). The assertion is internally
consistent but certifies the wrong function: with c = 7a/40−31/336 ≠ 0 the true
expanded second derivative carries an extra **24c/x²** term (from Q/x² with
Q = x⁴+ax²+c), i.e. the expanded form with −7x²−3a is exact only at a₀.
**Materiality:** none — the exact bound is assembled from the product-rule form
24[P″R + 2P′R′ + P·R″] − 2 with the correct P, and the numeric check uses the
true G_a; my residual computation confirms the defect is exactly
24c·(h″+1/x²). Fix the `g` line (or the assertion) before any formalization.

### Objection M2 (minor precision)

PROOF.md's ψ″ bound says "comparison of the decreasing cubic reciprocal with its
integral gives Σ ≤ 8 + ∫ = 10"; the integral is ∫₀^∞(t+1/2)⁻³dt = 2, so the bound
is f(0) + ∫₀^∞ = 8+2 = 10 — correct, but the writing should say the sum from n≥1
is bounded by the integral from 0. No mathematical error.

No other objections: all signs and parentheses of (3.3) match; the direction of the
refutation (sufficiency) is correctly identified; no endpoint or typo interpretation
is used; the numerical output is correctly quarantined as evidence-only.

## 3. Novelty gate — NO PRIOR RESOLUTION FOUND (bounded; not a certification)

- **Proof registries checked early and live:**
  - `suvrit/count-ex-machina` at head commit `dbf673741a54c7dc9d88a6aec0e8148a538f4a3a`
    (2026-09-09): full tree enumerated and `registry.json` read in full — 19 ledger
    entries, all matrix/optimization/quantum/geometry; **zero** entries touching
    psi/digamma/complete monotonicity/155-294.
  - `the-omega-institute/trureturing` mdbook open-problems index (live): no
    DeTemple/psi/digamma/155-294 entry (only unrelated "complete monotonicity of
    log-functions" items).
- **MathDB 328867**: open, no solutions/attempts (see §1).
- **All 14 OpenAlex citers screened** (`detemple-citers.json`, count = 14; no reliance
  on empty counts — records carry full metadata):
  - Full stored primary bodies grepped: Laplace2018 (1803.02513/JMAA),
    gamma2018 (1812.05343), incomplete2019 (JMI), landen2018 (MIA), psi2016 (JIA
    HTML), kgamma2020 (JIA HTML) — **none contains "155/294"** or any resolution.
    Specifically: Laplace2018's ψ-section (§4) proves monotonicity of
    Φ(x) = 1/R(x) − 24x² (Proposition 1, read in full) — a different function;
    psi2016 concerns exp(ψ(x+1/2) − 1/(24(x²+7/40))) − x; kgamma2020's conjecture
    mentions are unrelated citations.
  - Title/abstract screens of the remaining 8 (Landen/hypergeometric 2018,
    elliptic-integrals 2018/2020, hyperbolic-Taylor 2016, Gaussian-hypergeometric
    2021, divided-difference 2017, gamma-ratio-remainder 2022, Toader–Qi 2021,
    log/identric means 2025): none states or implies the G_a complete-monotonicity
    threshold. Matejíčka 2018 ("three conjectures… digamma") solves different
    conjectures (checked by abstract).
- **Targeted web queries** (8+ across two rounds, stored responseIds
  mvqojqz7yorsih, mvqovfmhqfnkdg, mvqovtkw6c1odo): no paper, preprint, registry,
  or MathDB resolution of Conjecture 1(ii) found; no author correction exists
  (arXiv v1 only; journal version identical).
- **Limits:** bounded-candid search; no priority claim; coverage of non-indexed or
  very recent literature is not guaranteed; this is *absence of evidence*, not a
  novelty certificate.

## 4. Substantive eligibility — ELIGIBLE

- The result is a **positive, strictly interior failure** (a = 527/1000 < 155/294,
  gap 31/147000) with an explicit rational witness and an exact positive gap
  510221/1093750 — not a mere endpoint/domain/typo correction, and not a limiting
  or boundary phenomenon.
- It refutes the sufficiency direction of a published iff-conjecture left open by
  its own authors in both the preprint and the journal version; it is not an
  immediate corollary of the paper's proved theorems (Theorem 4 concerns G_a, the
  paper proves only necessity for −G_a).
- The qualitative mechanism (G″_{a₀}(x) → +∞; FD midpoint-convexity failure at
  a₀) is a genuine structural strengthening beyond the single witness and is
  correctly scoped by the candidate.
- Standard scalar facts (ψ series, γ < 2/3, atanh log series) are credited
  ingredients, not discoveries — matching the candidate's own framing.

## 5. Recommendations to parent

1. Fix the `check_certificate.py` symbolic-identity defect (Objection M1) before
   any heavy formalization; keep the exact product-rule bound as the load-bearing
   certificate.
2. In any formalization, the FD route should use the literal `Complex.digamma`
   local analyticity at 1/2 (Gamma analytic, nonvanishing) as PROOF.md proposes;
   the a₀-scoping must be preserved (no all-a claim — see §2 probe).
3. Novelty status remains "no prior resolution found"; a final review should
   re-query MathDB/citers close to acceptance time.

## Artifacts (this lane)

- `review.md`, `provenance.json` — this review.
- `candidate-copy/` — byte copy of frozen candidate (hash-verified before/after).
- `evidence/independent_check.py` + `independent_check.output.txt` — 28/28 passing
  independent re-derivation (exact rational, symbolic, 80-dps numerical).
- `evidence/fd_and_scope_probes.py` + `fd_and_scope_probes.output.txt` — FD identity
  probe, G″_{a₀} divergence probe, and the a-scope refutation of the stronger claim.
