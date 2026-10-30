# Final adversarial five-gate review — DeTemple complete-monotonicity threshold (MathDB 328867)

Reviewer: pi-detemple-final-review (solo, no children, standard speed). Date: 2026-10-27.
Candidate: `../parent-detemple`, full45-file freeze `final-review-hashes.json`
(scope+hashes, frozen@fc9a7970e2; all45 current bytes verified independently before
and after all review activity). Credit0; accepted tally 24/30 untouched. AGENTS.md
and NEW/ledger.json (counting standard, accepted24/30) read in full first.

**Verdict summary**

| Gate | Verdict |
|---|---|
| Source | **PASS** |
| Mathematics | **PASS** |
| Formal (Lean) | **PASS** |
| Novelty / substantive | **PASS as bounded screen** (documented limits; no priority claim) |
| Manuscript | **PASS** |
| Reproducibility (fresh isolated strict replay) | **PASS** |

---

## 0. Byte provenance (own lane)

- Full byte copy: `bytes/parent-detemple/` (rsync from parent lane). All 45
  `final-review-hashes.json` entries re-hashed from my copy: **45/45 match**; re-verified
  unchanged after replay. No parent/shared edits, no staging/commits.
- Historical originals preserved: `check_certificate.py`/`certificate.json` retained
  unchanged (historical record, M1 defect superseded by PRELIMINARY-RECONCILIATION.md);
  original checker still runs (exit 0) but is not the current identity check.
- `check_certificate_corrected.py` rerun in my copy reproduces
  `corrected-certificate.json` **byte-identically** (diff clean).

## 1. Source gate — PASS

- Published Yang–Chu–Zhang, JIA 2015:157, DOI 10.1186/s13660-015-0674-8, **pages 12 and
  15 rendered and visually inspected by me** from the frozen page images
  (`sources/published-p12.png`, `published-p15.png`):
  - p12, Eq (3.3): `G_a(x) = 24(x^4 + a x^2 + (7/40)a − 31/336) R(x) − (x^2 − 7/40 + a)` — verbatim.
  - p12, Theorem 4: G_a strictly CM iff a ≥ 11165/8284 (about G_a, not −G_a; does not
    decide Conjecture 1(ii) and is not subsumed).
  - p15, Conjecture 1(ii): "**the function −G_a is completely monotone on (0,∞) iff
    a ≤ 155/294**" — verbatim; the paper itself proves only *necessity* (x→0⁺ ratio
    limit) and poses the conjecture as open.
- Preprint arXiv:1409.6411v1 text: Eq (1.10) R(x)=ψ(x+1/2)−ln x; Eq (3.3) and
  Conjecture 1(ii) identical; live abs page fetched today: **v1 only** (23 Sep 2014),
  no revision/withdrawal — current version confirmed.
- MathDB 328867 **fresh fetch today** (responseId mvqpvzstd9mtto): `status: open`,
  post_type conjecture, lean_formalization_count 0, **zero** solutions/comments/
  model_attempts/human_solves/replies/formulations; consistent with frozen
  `328867-live.json`.
- Preliminary reviewer SOURCE/MATH/ELIGIBLE PASS read in full
  (`reviews/preliminary/`); judged independently here; it supplies no final verdict.

## 2. Mathematics gate — PASS

Independent re-derivation (my own script, not the parent checker; exact fractions +
60-dps mpmath + SymPy):

- Witness: 155/294 − 527/1000 = 31/147000 > 0; x=1/50; P = 91379/525000000,
  P′ = 2639/125000, P″ = 2647/2500 (all re-derived exactly, all positive).
- ψ(1/2) = −γ−2ln2 ≈ −1.96351 > −31/15; ψ′>0; ψ″(z) = −2Σ(n+z)^{-3} ≥ −2·(8+2) = −20
  for z ≥ 1/2 (n=0 term 8, tail ≤ ∫₀^∞(t+1/2)^{-3}dt = 2; actual ψ″(1/2) ≈ −16.83);
  log 50 > 4658/1215 ≈ 3.8337 > 15/4 (atanh-series bounds 1123/1620 < 7/10 for ln 2
  and 1924/1215 for ln 5 re-derived). Hence R > 101/60, R′ ≥ −50, R″ ≥ 2480.
- Exact assembly: 24·(2647/2500)(101/60) − 48·(2639/125000)·50 +
  24·(91379/525000000)·2480 − 2 = **510221/1093750 ≈ 0.4664877 > 0** (matched to the
  exact fraction by independent common-denominator computation). So (−G_a)″(1/50) < 0
  and −G_{527/1000} is not completely monotone. 70-dps mpmath G″(1/50) ≈ 14.3299 >
  510221/1093750 (consistent; evidence only).
- Corrected checker identity verified by me symbolically: for general a, with
  c = 7a/40 − 31/336 and Q = x⁴+ax²+c, G_a″ = 24[(12x²+2a)h + (8x³+4ax)h′ + Q h″ −
  (12x²+2a)ln x − 7x² − 3a + c/x²] − 2 — exact residual 0 (the old checker's omitted-c
  defect is fixed; +c/x² present).
- Finite-difference route (the formalized one) verified numerically: D(x)/x² =
  24(regularPart + (−ln x)(50x²+2a)) − 2, residual 0 against direct evaluation.
  At a₀=155/294, c=0 exactly (7a₀/40 = 31/336), h continuous at 0, so D/x² → +∞;
  midpoint witnesses exist; D affine in a at fixed x gives a strictly interior
  0 < a < 155/294. **No all-a<a₀ or fixed-interior-divergence claim is made** —
  consistent with PRELIMINARY-RECONCILIATION.md M2.
- Paper Lemma limit B_c(x) → 2c·h(0) − 9c·log3 + 8c·log2 re-derived: correct.

## 3. Formal gate — PASS

- **Fresh isolated strict replay from MY byte-copy** via `verification/verify_candidate.py`
  with `--lean-bin .../lean-4.34.1-linux/bin/lean` and
  `--packages .../2026-10-14/formal/.lake/packages`:
  **PASS, 21 declarations, 3 modules** (SourceDefs, LogObstruction, SourceEndpoint);
  all three module logs **0 bytes**; warningsAsError=true; forbidden-token scan clean;
  only **propext / Classical.choice / Quot.sound**; no sorry/admit/axiom/unsafe/
  native_decide. Receipt `build/verified/audit.json` SHA256
  **72b9fb283c7587a4810655ba55a4138dcc4e49e6866114976a6e1b07e4fe5a19 — byte-identical
  to the parent receipt** (diff clean).
- All **21 actual type/axiom reports read** from my `Checks.log` (inventory below);
  statements match the claimed scope exactly.
- Load-bearing Mathlib lemmas independently verified in the pinned tree:
  - `contDiffOn_infty_iff_deriv_of_isOpen` (ContDiff/Deriv.lean): ContDiffOn ∞ f s ↔
    DifferentiableOn f s ∧ ContDiffOn ∞ (deriv f) s — used twice to reach deriv².
  - `convexOn_of_deriv2_nonneg'` (Convex/Deriv.lean): genuine second-derivative
    convexity criterion; `ConvexOn 𝕜 s f := Convex 𝕜 s ∧ (segment inequality)` — `.2`
    application in `source_interior_not_completelyMonotone` is the genuine midpoint
    contradiction (G(2x) < (G x + G 3x)/2 vs −G(2x) ≤ −(G x + G 3x)/2), closed by
    linarith against the witnessed strict inequality.
- Literal objects: `sourcePsi = deriv Real.Gamma / Real.Gamma` (exact source ψ);
  real/complex derivative bridge and continuity at 1/2 from actual complex Gamma
  analyticity (`Complex.differentiableAt_Gamma`) and nonvanishing; closed endpoints
  `source_interior_midpoint`, `source_interior_not_completelyMonotone`,
  `source_counterexample_328867ii` (premise-free negation of the literal iff).
  No residual hypotheses; no surrogate digamma; no source-normalization bridge.
- The rational a=527/1000, x=1/50 witness is correctly kept **math-only** (not a Lean
  endpoint); the paper says so explicitly.

Inventory (all 21): sourcePsi, sourceH, sourceR, sourceG, SourceCompletelyMonotone,
SourceConjecture328867ii, realGamma_deriv_eq_complex, gamma_analyticAt_half,
sourcePsi_continuousAt_half, sourceH_continuousAt_zero, boundaryModel, regularPart,
difference_identity, normalized_difference_tendsto, exists_boundary_midpoint,
sourceG_boundary, source_boundary_midpoint, source_interior_midpoint,
completelyMonotone_convex, source_interior_not_completelyMonotone,
source_counterexample_328867ii.

## 4. Novelty / substantive gate — PASS as bounded screen (explicit limits)

- **Fresh exact MathDB 328867 record** (all fields, today): open; zero resolutions of
  any kind; lean count 0; source = arXiv:1409.6411; current arXiv version v1.
- **Closest bodies newly read in full by me (beyond the preliminary 6):**
  - **Matejíčka 2018** (three conjectures, digamma/generalized digamma; JIA 2018:342,
    DOI 10.1186/s13660-018-1936-z): full body read from publisher HTML — disproves
    Yin et al. Conjecture 1 (φ_{p,k}), proves Yin Open Problem 1, disproves
    Chu–Zhang–Tang Conjecture 2, proves a logarithmic-mean ψ Theorem 1. **No
    155/294, no G_a, no CM threshold. Different theorems.**
  - **Yang–Tian, Czech. Math. J. 74 (2024) 337–351** (author follow-up; full 16-page
    DML-CZ PDF, sha 38340290…): CM of asymptotic-series remainders D_m(x;p,q) for
    ln Γ-ratios; **no 155/294, no G_a, no DeTemple** (grep-verified).
  - **Xu 2025** (Sharp bounds for the product and sum of logarithmic and identric
    means, BMMSS, DOI 10.1007/s40840-025-02023-z): full text read from Springer HTML —
    pure mean comparison chains; cites Yang–Chu–Zhang 2015 only for a hyperbolic
    Eq (2.9) bound. **No subsumption.**
- **Access limit (explicit):** Yang–Tian JMAA 517 (2023) 126649 ("Complete
  monotonicity of the remainder of the asymptotic series for the ratio of two gamma
  functions", OpenAlex W4293572007, one of the 14 citers) is **paywalled (HTTP 403)**;
  screened at title/abstract level only. Its closest same-family psi companion
  (CMJ 2024, same authors) was read in full and is clean, so subsumption risk is
  assessed as low but the body itself is unread. This is a documented coverage gap,
  not a finding.
- **Registries fresh:** `suvrit/count-ex-machina` registry.json fetched today and
  grepped — zero matches for digamma/psi/155/monotonic/DeTemple (all 19 entries are
  matrix/optimization/quantum/geometry). trureturing previously clean per preliminary.
- **Targeted queries today** (multiple engines): "155/294" surfaces nothing but the
  source itself and numeric trivia; no counterexample, correction, or resolution of
  Conjecture 1(ii) found anywhere. No inference drawn from empty counts or absent
  fractions beyond the explicit bodies read.
- Substantive eligibility: strictly interior positive failure with an explicit
  rational certificate and exact positive gap — not endpoint/domain/typo, not an
  immediate corollary of the paper's Theorem 4 or its necessity argument. The source
  proves only necessity; the candidate refutes sufficiency. **ELIGIBLE.**
- No worldwide-priority claim; MathSciNet/zbMATH unavailable; screen is bounded.

## 5. Manuscript gate — PASS

- Frozen `paper.pdf` sha256 **72271f3424a8c8618e417fd65de9c27ab40fa57e864566e629cd18d91e051590**
  (byte-verified in the 45). Both pages rendered by me (`evidence/paper-page-*.png`)
  and read: theorem statement matches the Lean endpoints (existential 0<a<155/294,
  strict midpoint failure, −G_a not convex/not CM); attribution correct (Eq 3.3 and
  Conjecture 1(ii) of Yang–Chu–Zhang 2015; preprint noted); part (i) explicitly not
  settled; rational witness correctly described as math-only; credit0 and no-priority
  language present; layout clean, references render, no clipping/undefined refs.
- Rebuild deemed unnecessary: tex sha af449450…, pdf sha 72271f34… both match the
  frozen map and qa (`paper-qa.json`: 2 pages, exit 0, no issues).

## 6. Strongest objections (recorded; none gating)

1. JMAA 2022 gamma-ratio-remainder body unread (paywalled) — closest same-family
   companion read in full is clean; residual subsumption risk assessed low but nonzero.
2. Novelty is absence-of-evidence from a bounded screen; no absolute priority.
3. The formal result is an existential strictly-interior parameter; no explicit
   minimal a, no exact replacement threshold, no part (i) — correctly not claimed.
4. The old no-Lean statements in PROOF/STATUS/provenance are historical and are
   superseded by FORMAL-ADDENDUM.md; the old finalreview-scope-pending wording is
   superseded by this review. Old25 originals remain byte-unchanged.

## 7. Recommendation

All five gates PASS for the current full45 freeze. Parent may proceed to deterministic
packet assembly and fresh extracted strict replay (parent-owned); candidate remains
credit0, accepted 24/30, with the documented novelty limits above.

## Artifacts (this lane)

- `bytes/parent-detemple/` — verified byte copy (pre/post hash-verified, 45/45).
- `evidence/` — paper renders, Yang–Tian CMJ 2024 PDF+txt (read in full),
  Matejíčka evidence note, download stubs, `evidence-hashes.txt`.
- `review.md`, `provenance.json` — this review and its provenance.
- `bytes/parent-detemple/build/verified/` — my replay receipt (SHA 72b9fb28…).
