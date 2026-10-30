# Independent FINAL five-gate review — parent-hermite-bound (frozen 66ecb8ce71)

Reviewer: pi final-review sub-agent (independent of the Pi author of the candidate and of the
Pi worker that produced Comparison.lean). Worked SOLO, no children. Own lane only:
`lanes/pi-hermite-final-review`. All 105 `full162-review-hashes.json` paths were byte-copied
(`candidate-copy/`), re-measured before review (`my-copy-hashes-pre-review.json`) and
re-measured after review: **0 missing, 0 mismatches, 0 post-review drift**. Frozen commit
66ecb8ce71 differs from HEAD 9359e1ba57 only by `NEXT.md` (verified by git diff), so the
working-tree candidate lane is the frozen bytes. Originals untouched. No shared/index/ledger
edits, no staging/commits/counts, no external posts.

## Gate 1 — SOURCE: PASS

- Publisher PDF `sources/hermite-published.pdf` (sha256 57fec518…b81, matches provenance.json),
  Commun. Theor. Phys. **73** (2021) 075002, **page 8 rendered at 150 dpi and personally read**:
  Conjecture 1, Eq. (29): |H_n(x)e^{−x²}| ≤ (2^nΓ((n+1)/2)/√π)·g_n(min(x, x_n))·e^{−x²/2},
  with g_n(x) = (1 − x²/(2n+1))^{−1/2} and x_n = √(2n+1)(1 − π/(2(2n+1))), for n ∈ ℕ⁺, x > 0;
  physicists' H_n(x) = (−1)^n e^{x²}(d/dx)^n e^{−x²} stated in the same page's text; authors note
  numerical checking "at least for n ≤ 20" and leave improvements "for future work".
- arXiv 2004.10441 **page 10 rendered and personally read**: Conjecture 1, Eq. (30) — literally
  identical statement (numbering shifts by one). Fresh fetch of https://arxiv.org/abs/2004.10441
  (2026-10-27): **v1 only** (22 Apr 2020), no revision, related DOI 10.1088/1572-9494/abf1dd.
- **Square-root cutoff verified literally against the publisher table**: Table 1 (p.9) lists
  x_n = 1.534, 2.052, 2.476, 2.843, … and g_n(x_n) = 1.374, 1.584, 1.772, 1.942, … for n = 2…10;
  I recomputed √(2n+1)(1−π/(2(2n+1))) and (1−x_n²/(2n+1))^{−1/2} — all match to the printed
  precision. The cutoff is a square root, not anything else.
- Fresh MathDB whole record refetched 2026-10-27
  (`fresh-sources/mathdb-346243-live.json`, sha256 3a4f357d…f7 full hash in provenance):
  id 20f4627d-53d8-417e-88db-8aff1596978e, **status "open"**, lean_formalization_count 0,
  comments/attachments/solutions/model_attempts/human_solves/formulations/replies/collections
  **all empty**, edited_at null. I inspected every array. Per the brief: open/empty status is
  source evidence, **not** novelty evidence.

## Gate 2 — MATH: PASS

I re-derived every load-bearing step from the actual Lean sources (2955 lines, 17 modules) and
verified the fine identities symbolically/numerically myself:

- **Duhamel identity** (Comparison.lean): the Wronskian combination
  sin(√q(x−s))g(s)+√q cos(√q(x−s))f(s) has derivative (s²−E+q)f(s)sin(√q(x−s)); FTC gives the
  exact variation-of-constants formula with **no sign or positivity premise**. I checked the
  Wronskian derivative by hand: correct.
- **First-zero positivity** (`odesys_pos`): genuine least-element-of-compact-closed-set
  contradiction (no positivity premise): if the bad set {δ≤x≤x₀ : f≤0} had least z, Duhamel at z
  with q=E has nonnegative integral (f>0 below z; √E·z ≤ √2 < π) and A·sin(√E z) > 0, forcing
  f(z) > 0. Correct, and it is a **lower** bound A/√E·sin(√E x) ≤ y — the direction fixed by
  PRELIMINARY-DECISION.md; the false preliminary upper-bound claim is not inherited anywhere in
  the candidate.
- **Upper sine comparison** on [0, x₀] via y''+q₀y = −(x₀²−x²)y with q₀ = E−2/E and nonpositive
  kernel integral — valid (all sine phases in [0, √2] ⊂ [0, π)).
- **Energy**: B = (E−x²)y²+y'², B' = −2xy² (re-derived). Strict loss
  B(x₀) ≤ A² − 25A²/(36E²) < A²(1−1/(2E²)); 25/36 > 1/2; ∫₁^√2 u sin²u du ≥ sin²1·½ > 25/72
  (sin1 ≈ 0.8415 ⇒ 0.708·0.5 = 0.354 > 0.347 ✓).
- **Wallis bridge**: I verified symbolically (sympy, exact):
  γ_{m+1}/γ_m − 1 = −1/(4(m+1)²(4m+7));
  δ_{m+1}/δ_m − 1 = (176m²+440m+247)/[4(m+1)²(4m+7)³(32m²+48m+17)];
  the paper's absolute form δ_{m+1}−δ_m = γ_m(176m²+440m+247)/[8(m+1)²(4m+3)²(4m+7)³] follows
  from 2E²−1 = 32m²+48m+17 (E=4m+3) ✓; γ_1 = 9π/28 ✓; γ_m − r_m < 0 numerically for m = 0…29;
  closed γ_m = π(2m+1)²C(2m,m)²/((4m+3)16^m) matches A²/(EC²) to 50 digits.
- **Tail (new route)**: Riccati t = p'/p, t' = 2xt−2n−t²; at a stationary point of the weighted
  Hermite (t = x): Σb² = q−1, Σb³ = x, Σb⁴ = (q²−1)/3 with q = E−x², b_i = (x−r_i)⁻¹ over the
  **actual real-root multiset** (roots with multiplicity; hermiteRatio_eq_rootMoment proved via
  eval_derivative_div_eval_of_ne_zero). Cauchy–Schwarz (Σb³)² ≤ (Σb²)(Σb⁴) gives 3E ≤ q³−q²+2q+1.
  I verified the rational certificate **exactly**:
  3E − F(22/7 − (22/7)²/(4E)) = [352947(E−7)⁴+6535179(E−7)³+40836159(E−7)²+89231464(E−7)+19560668]
  /(117649E³) > 0 for E ≥ 7, and π−π²/(4E) ≤ 22/7−(22/7)²/(4E) with difference
  (22/7−π)(4E−22/7−π)/(4E) ≥ 0. Since a_n² = E−π+π²/(4E), no nonzero stationary point exists at
  or beyond a_n (n ≥ 3, E ≥ 7); compact-maximum + polynomial·Gaussian decay gives the clamped
  tail. Numerical check: for n = 3,5,8,13,21 there are **zero** stationary points of
  H_n'−xH_n beyond a_n (brentq scan) — consistent.
- **Low degrees**: n=1 bulk πv(1−v/3) ≤ e^v (quadratic 1−15v/7+65v²/42 positive-discriminant ✓);
  global (2xe^{−x²/2})² ≤ 3/2 with (3/2)(1−a₁²/3) ≤ C₁² ⟺ 3π/8 < 4/π ✓; n=2 max(2, 8e^{−5/4})²
  with e^{5/2} > 4169/384 > 256/25 ✓ (8e^{−5/4} < 5/2). Both regimes are separately proved in
  Lean (LowDegrees bulk, LowTail global); the paper's compressed text matches.
- **Numerical sanity of the theorem itself** (not a proof): for n = 1…24, max over dense grids of
  |H_n e^{−x²}|/(C_n g_n(min(x,a_n)) e^{−x²/2}) ≤ 1, with ratio → 1 at x→0 for even n (constant
  is exactly sharp) — confirming the formal statement is the true tight conjecture, not a weaker
  variant. No vacuity.

No hidden assumed comparison/existence/tail facts found: the ODE premises of the generic lemmas
are instantiated with the actual signed Hermite functions via proved HasDerivAt instances and
exact initial values (InitialValues.lean, OddAssembly.lean).

## Gate 3 — FORMAL: PASS (fresh isolated replay on MY copy)

- Command exactly as briefed, on `candidate-copy/` (not parent oleans/logs). Result:
  **status PASS**, Lean 4.34.1 (commit 5045d005…), mathlib d13f23b723b8a846827a245b89c10fc7d3f11612
  + 8 dependencies hash-verified and unmodified. **162 declarations / 17 modules**, all module
  logs empty (warnings as errors), no forbidden tokens (sorry/admit/axiom/unsafe/native_decide —
  I scanned all 17 sources myself).
- I read **all 162** `#check`/`#print axioms` blocks from MY fresh
  `build/verified/Checks.log`: 162/162 depend only on [propext, Classical.choice, Quot.sound].
  Endpoint `HermiteEnvelope.source_conjecture_346243 : SourceConjecture346243` present and
  standard-3. `SourceConjecture346243` is the literal source statement (Rodrigues
  `sourceHermite`, `sourceCoefficient`, square-root `sourceCutoff`, `sourceEnvelope`,
  ∀ n ≥ 1, x > 0); `sourceHermite_eq_value` ties it to the polynomial recursion; no residual
  odd-bulk/comparison/loss premise (`source_conjecture_of_odd_bulk` is discharged by
  `source_odd_bulk_proved`).
- All 14 Comparison helpers exposed under `comparison_` names (rename map verified in
  comparison-integration.json; integrated sha 43db0036… matches the frozen hash), so all 25
  Comparison declarations are in the audit. My audit's 17 module hashes agree with the parent
  receipt `verification/full162-audit.json`; my own run is the authoritative evidence here.
  Isolation confirmed: the verifier builds only in `candidate-copy/build/verified` with LEAN_PATH
  pointing at the pinned packages.

## Gate 4 — NOVELTY / SUBSTANTIVE: PASS with explicit limits

I did **not** inherit the preliminary PASS and I did **not** inherit its classical-coverage
claims (rejected in PRELIMINARY-DECISION.md). My own subsumption attack used only valid
inequalities:

- **Foster–Krasikov 2000, Theorem 1 (pp. 307–308, actual PDF read by me)**: envelope valid only
  for x² < 2k−3/2, with a pole at y = 2k−x² → 3/2 denominator zero and a C(k) ≠ C_n constant.
  Numerically its RHS exceeds the target by huge factors near its validity edge and its value at
  the origin is not the sharp constant, so it alone cannot imply the literal conjecture, and it
  cannot repair the energy bound's √γ_m excess near the origin either (FK is not ≤ target there).
- **Szász/Cramer–Indritz (DLMF 18.14.9)**: |H_n e^{−x²/2}| ≤ √(2^n n!). Since
  2^n n!/C_n² > 1 for every n (checked n = 1,2,3 and asymptotically), this bound exceeds the
  target C_n g_n(min(x,a_n)) in a neighborhood of x = 0 (where the target equals C_n) — for every
  n. Hence **any min-combination of Szász with the pure energy bound fails**: the energy bound
  gives |y| ≤ √γ_m·C_n·g_n(x) with γ_m > 1 (verified γ_0 ≈ 1.047 > 1, γ_m → 1 from above), and
  the minimum of two bounds each exceeding the target near 0 still exceeds it. Removing the γ_m
  excess requires a strict energy loss; the only mechanism in the read literature that could do
  this is precisely the candidate's sine-comparison + Wallis bridge. Krasikov 2004 Thms 1–2 (read)
  are sup-type with non-sharp constants; Wang/Shi–Nemes–Wang–Wong 2023 Thm 3.1 (read) is
  asymptotic with error terms. Szegő 1975 pages 166/171/172/176/177/199/200 (per NOVELTY-R2, OSU
  Nevai OCR cache) contain no pointwise-sharp full-range envelope with these constants.
- **Independent widened search (2026-10-27, DuckDuckGo provider after Exa 429; queries on Guo-Liu
  resolution, Hermite envelope conjecture, weighted Hermite bound)**: no resolution or subsumer
  found; the top hit for every query is MathDB 346243 itself. arXiv 2004.10441 has no v2 and no
  author follow-up. OpenAlex citing corpus for W3019099826: 4 works (metadata inspected);
  NOVELTY-R2 additionally read 4 citer bodies + CEJ2024 + AIMS2024 statements and found no
  registry hits (pinned f8ffe9ed02 / 458aaeee…).
- **Honest limits**: the MDPI 2026 fractional-Hermite body remains **unread (HTTP 429)**; no
  MathSciNet/zbMATH sweep; my structural argument excludes the *named* classical bounds and their
  min-combinations, not every conceivable alternative proof by unrelated machinery. Open/empty
  MathDB status alone is not novelty evidence. This is a bounded screen, not a worldwide-priority
  certificate — consistent with the candidate's own claims (credit 0, no priority claim).

## Gate 5 — MANUSCRIPT: PASS

- main.tex sha256 3828c575…f4a5 ✓, paper.pdf sha256 ce0af69f…79f2 ✓ (both match the brief and
  paper-qa.json; paper.pdf byte-identical to build PDF per paper-qa.json).
- **All 3 pages rendered at 130 dpi and personally read.** Theorem 1 is the literal source
  statement; Eq (1)–(6) and the low-degree displays recomputed (see Gate 2) — all correct; the
  sine comparison is stated in the **correct (lower) direction**; the tail section states the
  real-root moment identities and the exact rational certificate I verified symbolically.
- Attribution: source due to Guo–Liu; classical identities, real-rootedness, oscillator
  comparison, Wallis, Taylor, Cauchy–Schwarz explicitly "not separately claimed results";
  Foster–Krasikov cited as a different envelope; **no worldwide-priority claim**; credit 0 and
  final-review-pending stated. No clipping, no undefined references; both references resolve.
- Optional tectonic rebuild not needed: stored PDF hash matches and paper-qa.json binds the
  clean build (exit 0, no issues); I did not rebuild and did not overwrite any original.

## Verdict

| Gate | Verdict |
|---|---|
| Source | PASS |
| Math | PASS |
| Formal (my fresh isolated replay) | PASS — 162/162, standard-3 axioms |
| Novelty/Substantive | PASS (bounded; limits recorded above) |
| Manuscript | PASS |

No decisive objection survived review. Residual limits are exactly the access-limited novelty
screen items above; none is a defect of the candidate's content. I made **no acceptance, no tally
change, no packet**: the parent owns the deterministic packet and extracted replay. Old19/126/135
historical incomplete statuses were treated as superseded by FULL162-INTEGRATION.md /
candidate.json / current manuscript and were not scored as gaps.
