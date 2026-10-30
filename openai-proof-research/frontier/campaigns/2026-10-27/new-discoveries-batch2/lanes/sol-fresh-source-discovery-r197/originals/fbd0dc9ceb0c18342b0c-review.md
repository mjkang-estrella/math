# Final five-gate review — parent-mills-cm (frozen at 5840569053)

Reviewer: pi final-review sub-agent (solo, no children, own lane
`lanes/pi-mills-cm-final-review` only, default speed). This is a NEW independent
final review, not a continuation of the preliminary reviewer. No external
messages, no git staging/commits, no shared or other-lane edits. Credit remains 0;
packet/count acceptance is not mine.

Scope: full five-gate review of the frozen 55-file evidence for the Ferreira–Simon
Conjecture 3 (arXiv:2108.09244v2 p.31; published Trans. Amer. Math. Soc. 376
(2023) 855–890, DOI 10.1090/tran/8748; MathDB 351688) n=0 refutation
F(x) = −r(x)²/r′(x) = r(x)²/(1−x·r(x)) via the fortieth-derivative obstruction.

## Gate verdicts

| Gate | Verdict | Summary |
|---|---|---|
| 1 SOURCE | **PASS** | Exact Conjecture 3 verified in BOTH arXiv v2 p.31 and — NEW — the published Transactions full text; published statement matches the preprint statement exactly. Prior 403 limit resolved. |
| 2 MATH | **PASS** | Independently rederived by two independent exact paths of my own (Leibniz recurrence and rational power-series division); all 41 table rows, D₄₀ = P(c²), exact Bernstein identity, π/2 interval, numeric spot check all agree. |
| 3 FORMAL | **PASS** | Fresh strict replay in my own lane from copied pinned bytes: 47/7 declarations, standard-3 axioms only, all module logs 0 bytes, receipt byte-identical to frozen parent receipt 81b42dd1…a63d. |
| 4 NOVELTY/ELIGIBILITY | **PASS** (bounded) | Same-author follow-up 2512.04940 read in full — no resolution/subsumption. Cambridge 2025 Meixner lead read — no relevance. OpenAlex fresh count 3 matches retained corpus. No MathSciNet/zbMATH/Scopus access; limits recorded. |
| 5 MANUSCRIPT | **PASS** | Both pages visually inspected; every claim maps to an actual Lean endpoint; no overclaims. Two minor stale-sentence findings (nonblocking) listed below. |

## GATE 1 — SOURCE: PASS

- Rendered and personally read PDF pages 29, 30, 31 of arXiv v2
  (source-pages/page-{29,30,31}.png): p.29 defines
  r(x) = e^{x²/2}∫_x^∞ e^{−t²/2}dt; p.30 Proposition 10 has the √z input
  ("For n = 0, 1 it is also LCM"); p.31 Conjecture 3 is
  z ↦ −(r^{(n)}(z))²/r^{(2n+1)}(z), "For every integer n", plain z, n=0 included,
  stated as an open problem with only simulation support. The intro fixes the CM
  convention on (0,∞).
- arXiv submission history fetched fresh: v1 2021-08-20, v2 2022-05-19 — v2 is
  the latest revision.
- **Journal body — resolved this review.** The frozen attempts (4 canonical PDF
  routes, all 403) did not include the AMS full-text HTML view
  `https://www.ams.org/journals/tran/2023-376-02/S0002-9947-2022-08748-1/viewer/`,
  which returns HTTP 200 with the complete published article body (11.8 MB HTML,
  saved as fresh/ams-viewer.html). From the published body I extracted:
  the identical definition of r; the published Conjecture 3 display formula
  (aria-label: z ↦ −(r^{(n)}(z))²/r^{(2n+1)}(z), plain z, "For every integer n");
  the CM-on-(0,∞) convention; and the published Proposition 10 with √z. The
  published statement matches arXiv v2 exactly. The embedded PDF permalink still
  serves a cookie shell, so PDF bytes remain unread, but the published full text
  has been read. The matching-abstract objection is moot: the matching *statement*
  was verified. No scope/priority obstacle from the published body remains.
- Unpaywall (fresh/unpaywall.json): the only OA copy anywhere is the arXiv
  submittedVersion (via HAL hal-04382024, no deposited file); no published-version
  repository copy exists — consistent with the above being the only legal body route.
- MathDB 351688 fetched fresh (fresh/mathdb-351688-final.json, HTTP 200): status
  open, progress null, and ALL of solutions / model_attempts / human_solves /
  formulations / attachments / comments / replies arrays empty;
  lean_formalization_count 0. Full record cross-checked against the frozen copy.

Decisive: source statement, domain, quantifiers (n ≥ 0 including 0), and the
√z Proposition 10 boundary all match the formalization.

## GATE 2 — MATH: PASS

I rederived everything by my own path, twice, without reusing the parent checker:

1. **Normalization/ODE.** r(0) = √(2π)/2 so r(0)² = π/2; differentiating the
   literal tail gives r′ = x·r − 1; hence r^{(k+2)}(0) = (k+1)·r^{(k)}(0),
   R₀ = c, R₁ = −1. All rederived independently.
2. **All 40 finite derivatives.** Two independent exact-ℚ computations of
   D₀,…,D₄₀ as polynomials in c:
   (a) the Leibniz recurrence D_{n+1} = Σ C(n+1,k)R_kR_{n+1−k} + (n+1)Σ C(n,k)R_kD_{n−k}
   with D₀ = c²; (b) exact rational power-series division r²/(1−xr) to order 40
   followed by multiplication by 40!. The two agree exactly, and **all 41 table
   rows** in formal/DerivativeTable.lean match my values row-by-row (I initially
   mismatched due to two bugs in my own checker — wrong D₀ and truncated degree —
   both mine, not theirs). D₄₀ is an even polynomial of degree 42 in c, i.e.
   degree 21 in c², matching derivative40-polynomial.json exactly.
3. **Actual derivative identification, not a surrogate.** The formal
   DerivativeIdentification proves `iteratedDeriv n quotient 0 = eval₂ (table poly n) (mills 0)`
   for all n ≤ 40 — genuine iterated derivatives of the genuine quotient.
4. **Bernstein certificate, my own exact verification.** P(a + (b−a)z) −
   Σ_k B_k z^k(1−z)^{21−k} = 0 verified as an exact identity over ℚ by my own
   binomial expansion (degree-by-degree), with B = Lean `bernsteinScaled` =
   frozen certificate `scaled_coefficients` = raw × C(21,k). All 22 B_k < 0.
   a = 392699/250000 = 1.570796 < π/2 = 1.5707963… < 1.5707965 = b (six-decimal
   bounds; mathlib Real.pi_gt_d6 / Real.pi_lt_d6 kernel-proves membership).
   P(π/2) = −24628065653022778370272.2022227366… < 0, matching the frozen decimal.
5. **Interval, not boundary.** F is C^∞ near 0 (denominator 1−x·r(x) → 1),
   so F^{(40)} and r′ are continuous at 0; with F^{(40)}(0) < 0 and r′(0) = −1 < 0
   there is δ > 0 with F^{(40)}(x) < 0 and r′(x) < 0 for all 0 < x < δ. Since 40 is
   even this violates (−1)^40 F^{(40)}(x) ≥ 0 at genuinely positive inputs. No
   boundary-only loophole; no float in any proof step (decimals only as orientation).
6. **Numeric spot check** (mpmath, 60 dps, independent series construction):
   F^{(40)}(0) = −24628065653022778370272.2022227… — agrees.

No minimal-order-40 claim is made anywhere; the proof only needs order 40.

## GATE 3 — FORMAL: PASS

- Copied all 55 pinned files from the frozen parent lane into my own lane;
  byte-identical SHA-256 for every file (final-review-hashes.json).
  (Operational note: the hashes file itself vanished once from my lane mid-review
  and was restored from the frozen parent; all 55 verified byte-identical after
  restore. Recorded in provenance.json.)
- Ran `verification/verify_candidate.py .` from my own lane with the explicit
  absolute `--lean-bin …/dlp-research/.tools/lean-4.34.1-linux/bin/lean` and
  `--packages …/2026-10-14/formal/.lake/packages`. The binary exists and ran
  (version 4.34.1, commit 5045d0056413…); all pinned dependency revisions verified
  clean by the script.
- Result: **PASS**, 47 declarations / 7 modules; all four main theorems present.
  I personally read **all 47 declaration types and every #print axioms line** from
  MY replay's Checks.log (build/verified/Checks.log): axioms are exactly
  {propext, Classical.choice, Quot.sound} (one declaration, the pure data
  `ratioDerivativeTable`, depends on no axioms); no sorry/admit/axiom/unsafe/
  native_decide (independent grep over formal/ is clean); warningAsError=true;
  all 7 module logs + Checks.log are 0 bytes except the intended Checks output.
- Literal-endpoint checks in the replayed source: `mills` is the literal improper
  Gaussian tail with a proved finite-integral bridge (Mills.lean);
  `bernsteinScaled_negative` is `decide +kernel`; `bernstein_identity` is an exact
  polynomial identity over ℝ for every real z; `SourceCompletelyMonotone` is
  literal C^∞ on Ioi 0 plus alternating-sign inequalities at all positive inputs;
  `sourceRatio n` is the literal source family for all n with `sourceRatio_zero`
  bridging n=0 to `quotient`; `source_counterexample_351688` is a closed
  premise-free negation of `SourceConjecture351688`;
  `regular_positive_interval_counterexample` closes with r′ < 0 **and** D₄₀ < 0 on
  a positive interval, no residual premises.
- **Determinism:** my receipt build/verified/audit.json has SHA-256
  81b42dd13d312ce43ddf6c3c6c5e851a18a2336fc0485a7163afa4ff7aa6363d — byte-identical
  to the frozen parent receipt (verification/parent-audit.json). The 42 MB
  DerivativeTable object compiled by kernel (no native/prebuilt substitution);
  replay completed in minutes.

## GATE 4 — NOVELTY / ELIGIBILITY: PASS (bounded)

- **Same-author follow-up 2512.04940** (Ferreira–Simon, "Mittag-Leffler functions
  and convex ordering", Dec 2025): downloaded and read the full body
  (fresh/2512.04940.pdf/.txt). It studies parameter-monotonicity of Mittag-Leffler
  functions; cites [FS23] only as a framework reference for comparison
  inequalities; contains zero mentions of Mills ratio, the derivative-ratio
  function, or Conjecture 3. No resolution or subsumption. Author's full
  publication list (pro.univ-lille.fr/thomas-simon/publications, 66 entries,
  read) contains no other Mills-ratio follow-up.
- **Cambridge 2025 lead** (Sakuma–Ueda, "Generalized Meixner-type free gamma
  distributions…", Canad. J. Math., S0008414X25101831, open access): full PDF
  publicly fetched and read (fresh/cambridge-meixner.pdf/.txt). Free-probability
  content; cites [FS23] only for "beta–gamma algebra" background (Section 6
  intro). No Mills content, no resolution. Not in the old OpenAlex 3 — the leads
  file was right that the indexed corpus is not the universe.
- **Closest Yang-type results re-inspected:** Yang 2507.10954 (retained source)
  concerns different weighted/square-root comparisons; the 2026 J. Inequal. Appl.
  higher-order-monotonicity paper (fresh/yang-higher-order.html) studies
  Y_{a,b}(x) = (x²+a)R²(x) + bxR(x) — different expressions, does not cite
  Ferreira–Simon, no conflict with F^{(40)} < 0.
- **Fresh citation-coverage check:** OpenAlex fresh query for DOI 10.1090/tran/8748
  returns cited_by_count 3 with exactly the three retained citers (2026 modified
  Bessel distributions PJM; 2025 unimodality preservation Results in Math.; 2026
  positive Fox H-functions). No empty-search inference: every lead's body was read.
- **Exact-source-problem searches:** no hit anywhere for a resolution, refutation,
  or counterexample of the derivative-ratio conjecture; arXiv 1305.5429
  (Gasull–Uzet, withdrawn) proves r itself CM — orthogonal and no conflict.
- **Recorded limits (candid):** no MathSciNet or zbMATH access; Scopus not
  directly accessible (the Lisbon record's "Scopus 5" vs OpenAlex 3 discrepancy is
  noted, not resolved; index coverages differ and I do not claim 3 exhaustive);
  no worldwide-priority guarantee. Bounded screen only, as designed.
- **Nonblocking observation:** sources/fox2502.10483 ("positive Fox H-functions")
  does not actually cite Ferreira–Simon anywhere in its body or reference list
  (checked full text); the OpenAlex linkage appears erroneous. This does not
  affect screening (absence of citation cannot resolve the conjecture) but the
  "three citers" count should be read as two real citers plus one erroneous link.

No subsuming or resolving work was found; nothing excludes the candidate.

## GATE 5 — MANUSCRIPT: PASS

- Hashes verified: main.tex 816f485e…842a, paper.pdf a8d9a0ec…d133 (byte-identical
  to frozen pins; original PDF untouched by me).
- Both pages rendered at 130 dpi and visually inspected page by page
  (fresh/mp-1.png, fresh/mp-2.png): clean two-page letter layout, no clipping,
  no undefined references, correct numbering.
- Claim-to-endpoint mapping (all verified against my replay):
  Eq.(1) ↔ `MillsCounterexample.mills` (literal improper integral);
  CM definition ↔ `SourceCompletelyMonotone` (smoothness + (−1)^k signs on (0,∞));
  the stated conjecture ↔ `SourceConjecture351688`/`sourceRatio` (paper says
  "nonnegative integer n", the source's "every integer n" is only meaningful for
  n ≥ 0 — faithful); Eq.(2) ↔ `quotient_eq`; Theorem 1 ↔
  `regular_positive_interval_counterexample`; "Proposition 10 … after composition
  with x ↦ √x" is stated correctly and is not contradicted; endpoint named in the
  text is exactly `MillsCounterexample.source_counterexample_351688`, described as
  premise-free — true in my replay. "47 declarations in seven modules, Lean
  4.34.1, mathlib d13f23b7" all match. The Cauchy-quadrature number is presented
  as a non-proof diagnostic — honest. No all-n claim, no minimality claim, no
  absolute-priority claim; scope sentences are accurate.
- Numerical claims checked: leading coefficient of P equals 40! ✓; P(π/2) ≈
  −2.4628065653022778370×10²² ✓; bound (9) −2463·10¹⁹ < B_k < −2460·10¹⁹ for all
  22 indices re-verified by my own exact rational arithmetic ✓; "3.141592 < π <
  3.141593" ✓.
- **Clean Tectonic rebuild:** via the 2026-10-25 build_paper.py into my own
  `rebuild/` (cached bundle): exit 0, zero issues, text-extraction MD5 of the
  rebuild equals that of paper.pdf (embedded /ID differs only, per packet rule).
  Original paper.pdf bytes unchanged.
- **Nonblocking findings for the parent (small text fixes):**
  1. Page 2, §3: "The source comparison uses the latest arXiv v2: the published
     full-text access limit is recorded." — superseded: this review has now read
     the published full text via the AMS HTML view and verified the published
     Conjecture 3 matches arXiv v2 exactly. Parent should update this sentence
     (and README.md / provenance.json `published_body_access`) to reflect the
     resolved access; this only strengthens the result.
  2. Page 2, §3: "The bounded prior-work investigation and independent review
     remain pending for this draft" — process-stale once this review lands;
     parent should update with the final review reference. Cosmetic.
  3. Novelty narrative (not in the paper itself): the fox paper is an erroneous
     OpenAlex citership (see Gate 4).

## Overall

**Five-gate verdict: PASS / PASS / PASS / PASS / PASS. No HOLD, no FAIL.**
Decisive strengths: literal source endpoint verified in both preprint and
published body; two independent exact rederivations of the entire finite
derivative table and certificate; deterministic fresh strict replay identical to
the frozen receipt; no prior art found in the (bounded) screened corpus; clean,
accurate two-page manuscript. The former material journal-access limit is resolved
by this review. Remaining limits are the standard ones (no MathSciNet/zbMATH/
Scopus, no priority guarantee) and do not block.

Recommended for parent: proceed to final deterministic packet extraction replay
and (if policy allows) count-credit decision; apply the three small manuscript/
provenance text updates above.

## Evidence inventory (own lane)

- Replay: build/verified/audit.json (SHA 81b42dd1…), build/verified/Checks.log
  (all 47 types + axioms), final-replay-stdout.log / final-replay-stderr.log.
- Hashes: final-review-hashes.json (+ fresh/final-review-hashes-copy.json backup).
- Source: source-pages/page-{29,30,31}.png; fresh/ams-viewer.html (published body);
  fresh/tran-8748-published.pdf (cookie shell, PDF route still blocked);
  fresh/unpaywall.json; fresh/hal.json; fresh/mathdb-351688-final.json;
  source-access-r2/final-access-record.md.
- Math: my checker transcripts in this review; fresh/bernstein-extracted.txt.
- Novelty: fresh/2512.04940.pdf/.txt; fresh/cambridge-meixner.pdf/.txt;
  fresh/yang-higher-order.html; fresh/openalex-fresh.json.
- Manuscript: fresh/mp-1.png, fresh/mp-2.png; rebuild/build/{main.pdf,paper-build.json}.
