# Independent FINAL adversarial review — Hetyei Conjecture 6.10 / MathDB 319292 (parent-flat-bernoulli @ 91b28f08e6)

Reviewer lane: `pi-hetyei-final-review`. Work SOLO, no children, no git actions, no parent/shared edits.
Basis: my own byte copy `candidate-copy/` of the complete candidate (69 frozen hashes re-verified
on the copy AND re-verified on the parent lane at review end — 0 mismatches). This is a NEW review,
not a read-through of the preliminary review at `pi-hetyei-preliminary-review`.

Candidate: `Hetyei Conjecture 6.10 / MathDB 319292`. Accepted 21/30 campaign; this candidate credit 0.
I do not count or accept it; this review gates only.

## Exact result under review

`FlatBernoulli.source_conjecture_319292 (n : ℕ) (hn : 12 ≤ n) : sourceKappa n < n * sourceKappa (n-1)`,
where `sourceK` is the literal finite ordered-composition factorial sum of source eq. (16) over
`Composition n` with blocks ≥ 2 (empty composition contributes 1 at n=0), and
`sourceKappa n := n * sourceK (n-1)` (the source-proved count relation). Equivalently
`source_K_tail : sourceK n < n * sourceK (n-1)` for n ≥ 11. This is Hetyei arXiv:0912.0573v1,
printed p.19 Conjecture 6.10: `n·κ_{n-1} > κ_n` for n ≥ 12, equivalently `n·K_{n-1} > K_n` for n ≥ 11.

## Gate 1 — SOURCE: **PASS**

- I personally rendered and read printed pages 18, 19, 20 from my own copies (both the frozen
  `source-page19/20.png` and fresh `pdftoppm` renders `my-page17-18.png`, `my-page18-19.png`,
  `my-page19-20.png` from the frozen PDF).
- Conjecture 6.10 printed exactly as claimed (p.19): "For n ≥ 12 we have n·κ_{n−1} > κ_n.
  Equivalently, n·K_{n−1} > K_n holds for n ≥ 11." No extra hypotheses (no spectral, moment,
  existence, recurrence, or source assumptions anywhere in the statement).
- Eq. (16) printed p.18 matches the candidate's K display: ordered compositions m₁+⋯+m_k=n,
  m_i ≥ 2, multinomial × ∏(m_i−2)!, "for n ≥ 0", with K_n = κ_{n+1}/(n+1). The printed inner
  sum (k=1..⌊n/2⌋) is empty at n=0 while κ₁ gives K₀=1; the candidate's empty-composition
  convention (K₀=1) is exactly consistent with generating function (17) (constant term 1) and
  Proposition 6.7 ("the empty word is a valid position" — a kernel position of rank 0). This is a
  consistent convention, not a source typo fix, and no credit is claimed for it.
- Lemma 6.9 (a_n = (−1)ⁿ(K_n − n·K_{n−1}), coefficient of tⁿ/n! in 1/(1−ln(1+t))) and eq. (21)
  match the candidate's normalization; b_n = (K_n − nK_{n−1})/n! and the target is b_n < 0, n ≥ 11.
- Printed eq. (23) on p.20 indeed carries the opposite sign to the conjecture (from (22),
  (−1)ⁿ∫₀^∞ x(x−1)⋯(x−n+1)e^{−x}dx = (−1)ⁿ(K_n−nK_{n−1}), so the printed "(−1)ⁿ ∫ > 0" is
  equivalent to K_n − nK_{n−1} > 0, the reverse of the conjecture). The candidate correctly
  declines to claim (23) and takes no credit for the discrepancy.
- MathDB 319292 live JSON (frozen): statement matches the source; status open; "supplied text
  gives no resolution"; lean_formalization_count 0. Note MathDB also cites arXiv:math/0202304 as
  an earlier stating paper (2002); my checks found no resolution there either.
- arXiv history: 0912.0573 has only v1 (3 Dec 2009); journal ref JCTA 117(8) 2010, 1107–1126.
  The author never retracted or resolved the conjecture on arXiv.

## Gate 2 — MATH: **PASS**

Independently recomputed everything from scratch (exact rational arithmetic + hand proofs):

- Recurrence: (1−t)(1−ln(1−t)) = 1 − Σ_{j≥2} t^j/(j(j−1)), so U(t)=1/((1−t)(1−ln(1−t))) gives
  u_{n+2} = Σ_{k=0}^{n} u_{n−k}/((k+2)(k+1)), u₀=1, u₁=0. Verified.
- Exact values: b₃ = −1/3; b₁₂ = −10819/9979200 < −1/2000; b₁₄ = −3676549/1816214400;
  b₁₄−b₁₂ = −1707491/1816214400 < 0 — all reproduced exactly; b_n < 0 for every n ≥ 11 confirmed
  by exact rational computation to n=38 (evidence only; the proof is the spectral argument).
- K_11 = 8738016, K_12 = 104336880 match OEIS A089064/A006252 cross-values; a₁₁ = +319296,
  a₁₂ = −519312 match OEIS A006252 exactly.
- Propagation criterion re-derived by hand: even split b_{12+2m} = q^{2m}(T−S_m) verified
  (λ^{11+2m} bookkeeping), S₀ = T−b₁₂, and b₁₂<0 with 0<q²≤1 gives b₁₂ ≤ q²b₁₂, hence S₁ ≥ S₀;
  z^m ≥ 1+m(z−1) on z≥0 (tangent line of the convex integer power) gives S_m ≥ S₀ and
  b_{12+2m} ≤ −c·4^{−m} (using q ≥ 1/2). Odd: d_λ = w_λ(1−λ) has mass 1 (mean 0) and
  Σd_λλ² = −b₃ ≥ 1/4; normalizing z_λ = 4λ² is genuinely needed (the paper's D1 fix is correct
  and necessary); gives b_{2m+1} ≤ −4^{−m} for all m ≥ 0, covering n = 11.
- Existence/uniqueness of the negative eigenvalue: mean 0 + second moment (N+1)/(2N) ≥ 1/2 > 0
  forces a negative spectral value; a=0 subspace is PSD so two negative eigenvectors
  (with multiplicity) would give a nonzero center-free combination with negative form — sound.
- q ≥ 1/2 from λ² ≤ (1−q)λ+q averaged — verified.
- Convolution (5): solved the node recurrence by hand; a_{n+2} = Σ p_k^{(N)} a_{n−k} exact. ✓
- Faulhaber display verified for k=0,1,2 and against mathlib `sum_range_pow` semantics;
  p_k^{(N)} = M_N(k)−M_N(k+1) → 1/((k+2)(k+1)). No Riemann premise.
- Numeric matrix checks (my own): spectrum ⊆ [−1,1] and exactly one negative eigenvalue for
  N = 1,2,3,5,50 (degenerate N=1 included); center moments match; b_n^{(N)} fails the criterion
  hypotheses only for small N, exactly as the proof's "eventually" structure requires; the
  criterion bounds are uniform in N and survive the limit. u_n^{(400)} within 1.4e−3 of u_n.
- Analytic cross-check §5 (explicitly not needed by the spectral route): certificate J > 1/400
  and J > (2719/1000)/(1718/1000)^13 verified exactly; numeric I₁₂ ≈ 0.003472 >
  e/(e−1)^13 ≈ 0.002388 consistent.

No gap found. The three exact checks (b₃, b₁₂, b₁₄) are the only input data; everything else is proved.

## Gate 3 — FORMAL: **PASS**

- I copied ALL candidate bytes myself and ran `verification/verify_candidate.py` (my copy) with
  the pinned ABS Lean bin `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`
  and ABS packages `.../2026-10-14/formal/.lake/packages` on MY copy. Pins verified (Lean 4.34.1,
  mathlib d13f23b7 + 8 deps at recorded revisions, clean status). Objects cleaned; compiled with
  `-DwarningAsError=true`.
- Result: **PASS, 117 declarations / 16 modules**, manifest = the 16 `.lean` files; forbidden
  tokens (sorry/admit/axiom/unsafe/native_decide) absent by scan; standard 3 axioms only
  (propext, Classical.choice, Quot.sound; two declarations need only propext+Quot.sound).
- I read all 117 actual type + axiom reports in my own `build/verified/Checks.log` (351 lines)
  and the receipt `audit.json` — its SHA256 is **366e3c34a95b54f7047b2a47e8fa1a40717fc52e473dc97dcd478f148ae9c473**,
  byte-identical to the parent's receipt: the fresh isolated replay is deterministic and reproduced.
- I read the actual sources of every load-bearing bridge:
  - `SourceCompositions`: `prependComposition` Σ-type bijection (injective+surjective proved);
    singleton blocks get weight 0 so the all-blocks sum literally equals the blocks≥2 sum;
    recurrence proved; `normalizedComposition 0 = 1`.
  - `SourceCounts`: `sourceK` is the literal finite sum over `Composition n` of n!/(∏m_i!)·∏(m_i−2)!
    (0 for invalid); factorial-ratio bridge `blockWeight b = (b−2)!/b!`; `sourceK_eq_renewal`;
    exact rank shift in `source_K_tail`; `sourceKappa` defined by the source-proved relation.
  - `Arrowhead`/`SpectralCompression`/`ArrowheadSpectral`: actual `Matrix (Option ι)` arrowhead,
    two explicit SOS identities, spectral interval from the SOS, `negative_eigenindex_unique`
    INCLUDING multiplicity via genuine OrthonormalBasis eigen-decomposition of the actual
    Hermitian matrix; center weights are squared inner products (nonnegative, mass 1, mean 0,
    second moment = Σv_i²).
  - `ArrowheadCriterion`: q from actual eigenvalues (1/2 ≤ q ≤ 1); even/odd quantitative bounds.
  - `ArrowheadGrid`/`ArrowheadRecurrence`: actual gridNode = i/N, gridV = sqrt((1−t)/N);
    Σv_i² = (N+1)/(2N) exactly; exact center walk convolution proved from the actual matrix
    action, no analytic inverse assumed.
  - `GridPowerLimits`/`GridKernel`: mathlib `sum_range_pow` (Faulhaber) pinned; polynomial in
    1/N; exact limit 1/((k+2)(k+1)); `gridMoment_tendsto` by strong induction through the exact
    convolution.
  - `RecurrenceBase`: renewal values 0..14 kernel-checked (`norm_num` off the recursive def);
    the three strict base facts are exact `norm_num` consequences.
  - `RenewalTail`: uniform bounds propagated via `Filter.Tendsto.eventually_lt_const` +
    `le_of_tendsto` — the "eventual N" bookkeeping is correct; even/odd case split covers all
    n ≥ 11 with strict negativity.
- No assumed Riemann/spectral-measure/generating-function premise anywhere in the dependency
  chain; degenerate N=1 and repeated eigenvalues are handled by the general arguments.
- `formal-dev` exploratory files are outside the certificate (manifest determines the 16 modules) — confirmed.

## Gate 4 — bounded NOVELTY / ELIGIBILITY: **PASS (bounded)**

Independent searches (own queries, incl. OEIS live, arXiv, renewal-theory literature, GitHub):

- OEIS A006252 (live, edited Sep 2026): lists the exact signed sequence (…, 319296, −519312, …);
  entry gives a factorial-series E₁ representation; **no proof of the continued alternation**.
  A006252 has negative entries — independently confirming the parent addendum's point 3 that the
  Benyi–Yaqubi printed identification cannot be a literal nonnegative enumeration of the full
  signed sequence.
- No hit for "novice's chance" / Conjecture 6.10 resolutions; no Lean formalization of this
  result found on public GitHub; no registry (trureturing/Zetalaw/count-ex-machina) hit.
- 4 OpenAlex citers of 0912.0573 (Sterling IJGT 2017 — paywalled; q-hypergeometric Bernoulli
  2021; domino shave 2022; Timber DAM 2017): parent's fetched texts contain no engagement with
  Conjecture 6.10 (I grepped the frozen citer texts myself).
- Weniger 1005.0466v1 (fetched): factorial-series/Stirling numerical-analysis paper; consistent
  with "shares the same numbers via (18)-type formulas, no tail proof". Same-numbers prior art,
  not a subsumption.
- Classical subsumption scrutinized: the normalized sequence is the renewal sequence of the
  interarrival pmf p_j = 1/(j(j−1)), j ≥ 2 (survival P(X>n) = 1/n, infinite mean Σ j·p_j = ∞).
  u is not globally decreasing (u₂ > u₁), so any global-monotonicity theorem cannot apply as
  stated; known finite-mean frameworks (Hansen, f_n = p_{n+1} ⇒ f₀=0, f₁=1/2) fail at the
  boundary and by the infinite mean. I located no transformed/eventual classical theorem giving
  eventual strict decrease for this distribution. I verify the addendum's derivative correction:
  d/dx [1/(x(1−log x))] = log x/(x²(1−log x)²) (positive for x>1, f<0 for x>e) — the correction
  is right and still defeats any nonnegative CM representation; non-load-bearing either way.
- Last Lin / Baskakov exclusion: outside this candidate's target; parent's screen r7 records a
  public prior refutation at an immutable commit; no impact here.
- Eligibility: the endpoint is the literal all-order source question with ONLY the rank
  hypothesis, resolved via a new finite-matrix spectral propagation mechanism; not a finite
  check, not a helper, not a typo fix (the (23) sign and the K₀ convention are explicitly not
  counted). The original game-position type and the author's enumeration theorem are credited
  upstream, not recoded — the disclosed scope is accurate and appropriate: the count sequence is
  fully determined by the source's own formulas, and every bridge from the literal formula (16)
  is proved. Honest limits kept: JCTA published body and Sterling 2018 paywalled; Timber fetched
  is the thesis (author chapter), not the final journal body; no global priority claim.

## Gate 5 — MANUSCRIPT: **PASS**

- I rendered and personally inspected all 3 pages of my copied frozen `paper.pdf`
  (SHA 913aed98…, matching final-review-hashes.json and paper-qa.json, which records current
  tex/pdf hashes and the 366e3c34… receipt). Clean render; no clipping/overfull/undefined refs.
- Every display recomputed against my own arithmetic and the actual Lean endpoint: (1) matches
  source (16); (2) recurrence exact; (3) exact rational values exact; Lemma 2 statement/proof
  correct including the D1 normalized-variable step and the D2 explicit negative chain
  (b₁₂ ≤ q²b₁₂ via 0<q²≤1); (5) convolution exact; Faulhaber display verified; final bounds and
  "every integer n ≥ 11 is covered" correct.
- Scope statements are accurate: 117/16, endpoint only n≥12 hypothesis, game-position type and
  source enumeration theorem not re-formalized, classical ingredients credited, credit 0, (23)
  not counted, access limits disclosed. Formal game-count representation scope is accurately
  described ("Our formalization starts from the explicit finite formula").
- No manuscript edits made by me. Separate cosmetic notes for the parent (no gate impact):
  1. §4 reuses `a_n` for u_n^{(N)} while §1/§3 use a_n in the source's sense — mild notation
     collision; suggest renaming (e.g. A_n) in a future revision.
  2. Abstract says "must be negative" — fine as proved, but consider "are negative" for tone.
  3. p.1 "∑ u_n t^n" line has tight spacing after normalization — cosmetic only.

## Verdict

| Gate | Verdict |
|---|---|
| SOURCE | PASS |
| MATH | PASS |
| FORMAL | PASS |
| bounded NOVELTY / ELIGIBILITY | PASS (bounded) |
| MANUSCRIPT | PASS |

No decisive objections. The candidate is recommended to the parent for deterministic packet
assembly and acceptance decision; per instructions I do not count or accept it, and credit
remains 0 pending the parent's process.

## Candid limits of this review

- Published JCTA body (403) and Sterling 2018 remained inaccessible to me too; Timber evidence
  is thesis-chapter only. A hypothetical published resolution there is not excluded by my review.
- Web search provider rate limits forced provider fallbacks; my coverage of the open web is
  broad but not exhaustive; no worldwide-priority claim is made or certified.
- I did not re-verify the mathlib `sum_range_pow` internals (pinned mathlib is trusted
  infrastructure per AGENTS.md upstream-truth policy).
- My novelty searches are keyword-based; a resolution under different vocabulary could exist.
