# Independent Final Review — parent-bessel-fejer (Bessel–Fourier modified Fejér kernel refutation)

Reviewer: pi-bessel-fejer-final-review (solo, no children). Date: 2026-10-27.
Frozen candidate: NEW/lanes/parent-bessel-fejer, frozen commit 26b211919f, authoritative
manifest final-review-hashes.json (56 paths). My byte copy: this lane/own-copy/ — all 56
SHA-256 verified against the manifest BEFORE and AFTER all reads (56/56 both times;
candidate lane untouched). paper.pdf sha256 099c7b02325fd9763789fd8667c3868695d58ff852f1198cbd2160b1441863c9.

ONE proposed outcome: refutation of Acosta Babb's Bessel–Fourier modified Fejér-kernel
nonnegativity conjecture (MathDB 365454; arXiv:2410.17681v1 Conjecture 1 p10; published
JMAA 559 (2026) 130440, Conjecture 1 p11), via the strictly interior two-term witness
K^{2/5}_2(47/50) < −1/500. No priority claim. Credit 0. Accepted tally untouched.

## Gate 1 — SOURCE: PASS

- Visually read genuine publisher pages from my own copy: published-p7.png (kernel
  definition K^a_{nu,M}(x) := sum_{m<=M} (1 − m/(M+1)) j_{nu,m}^a J_nu(j_{nu,m} x);
  K_{nu,0} ≡ 1 convention), published-p11.png (Section 5, Conjecture 1: "For all
  0 <= a <= 1/2, M ∈ N and x ∈ [0,1], K^a_{nu,M}(x) >= 0"; Fig 1 shows only M=10,100,1000
  at a=1/2), arxiv-p10.png (Conjecture 1 for the order-zero kernel K^a_M). Running heads
  confirm J. Math. Anal. Appl. 559 (2026) 130440; PDF contains the Elsevier DOI link;
  14 pages. Text extraction cross-checked in sources/*.txt.
- Normalization/quantifiers match the candidate exactly; the M=0 ≡ 1 convention is in the
  source and in Lean sourceKernel. The published conjecture display retains nu; Section 5
  fixes nu = 0, and the MathDB record describes the order-zero kernel. The nu=0 instance is
  in scope under every reading (if nu were universally quantified, our witness refutes a
  fortiori). arXiv history: v1 only (verified via arXiv API).
- Fresh complete MathDB activity record fetched by me (not inherited): mathdb.com/api/posts/365454
  → status "open", post_type "conjecture", solutions/model_attempts/human_solves/replies/
  comments all empty, lean_formalization_count 0. Saved as evidence-mathdb-fresh-365454.json.
  Open label is NOT treated as novelty evidence.

## Gate 2 — MATH: PASS

Built my own exact checker from scratch (my-math-check.py, Fraction arithmetic; NOT derived
from exact_bessel_certificate.py). All checks PASS:

1. Defining series: J0(x) = sum (−1)^k q^k/(k!)^2, J0'(x) = −(x/2)H(x^2/4), q=x^2/4.
   Normal convergence by ratio test. Tails: for |q| <= 9, term ratio <= 9/441 < 1/2 from
   index 20, so |J0 − p| <= 2·9^20/(20!)^2 ≈ 4.1e−18 < 1e−17 and |H − h| <= 2·9^20/(20!·21!)
   ≈ 2.0e−19 < 1e−18. Geometric-tail argument rederived independently; bound is sound.
2. All five table rows re-proved by my own exact Bernstein conversion (degree 19) with the
   standard coefficient formula — bounds 1/5, −1/50000, −3/25, 3081/40000, −11381/100000
   each hold with margins far above the uniform tails. Whole-interval (no grid).
3. Zero identification without assuming approximate roots: endpoint signs J0(2.4048)>0,
   J0(2.4049)<0, J0(5.5200)<0, J0(5.5201)>0 via p ± e; H>0 on q∈[0,9/4] ⇒ J0 strictly
   decreasing on [0,3] (J0(3)<0 checked); J0<0 on [3, 5.5200]; J0 strictly increasing on
   [5.5200,5.5201]. Hence exactly one zero in (0,3] (inside [2.4048,2.4049]), none in
   [3,5.5200], exactly one in [5.5200,5.5201] — these are precisely the first two positive
   zeros (IVT + strict monotonicity + negative middle interval). Verified as a complete
   case analysis; matches Lean first_root_least/second_root_least.
4. Fifth-power bounds are literal positive-real-power comparisons (exact): 1.4204^5 < 2.4048^2,
   2.4049^2 < 1.4205^5, 1.9805^5 < 5.5200^2, 5.5201^2 < 1.9806^5; (j^{2/5})^5 = j^2 gives
   j1^{2/5} ∈ [1.4204,1.4205], j2^{2/5} ∈ [1.9805,1.9806]. Sign handling in the final bound
   (upper bound of a positive-weight × negative-value product uses the SMALLER power factor
   and the negative upper bound) is correct.
5. Final evaluation by my own exact interval Horner on the two scaled q-intervals:
   J0(c·j1) ∈ [0.076913028, 0.077024111], J0(c·j2) ∈ [−0.114408808, −0.113822344],
   K ∈ [−0.002697371, −0.002203679] — strictly below −1/500 = −0.002, and tighter than the
   paper's −653867/300000000 = −0.002179557 (also verified by exact hand computation:
   (2/3)(14205/10^4)(7703/10^5) − (1/3)(19805/10^4)(569/5000) = −653867/3e9·... ✓).
   Certificate JSON kernel_interval_decimal [−0.0027011851, −0.0021998847] contains my
   interval; consistent.
6. Independent high-precision cross-check (mpmath, 60 dps, zeros by verified bisection):
   K(2/5,2,47/50) = −0.0024300620 lies inside my exact interval; j1 = 2.4048255577,
   j2 = 5.5200781103 inside the enclosures. Redundant witness K(1/2,2,9/10) = −0.012550791
   matches the certificate half-power interval [−0.012817, −0.012319].
7. Divergence-of-methods note confirmed: my checker uses interval Horner, Lean uses
   Bernstein for final evaluations — both give the same strictly interior theorem.

Caveat recorded: an earlier quick probe of mine gave a wrong M=100 negative value due to
sloppy root-finding; after verifying zeros rigorously, values agree with the source's
Fig 1 (kernel positive at plotted resolution for M ≥ 10). This was my error, not the
candidate's; the candidate's zero identification is exact, not numerical.

## Gate 3 — FORMAL: PASS

- Fresh isolated strict replay run by me on MY byte copy with the pinned command
  (verify_candidate.py ABS_COPY --packages 2026-10-14/formal/.lake/packages
  --lean-bin dlp-research/.tools/lean-4.34.1-linux/bin/lean): TERMINAL PASS.
  My receipt build/verified/audit.json sha256 65b88b000b9dc8e42e41305bab83ebd1cc5aef91ffb00a054103992cbcf2fab5
  — byte-identical to the parent87 receipt. 87 declarations / 8 modules; all module source
  hashes equal final-review-hashes.json entries; all 8 module logs empty under
  warningAsError=true; compiler 4.34.1 and all 9 pinned dependency revisions verified by
  the script; forbidden-token scan clean (no sorry/admit/axiom/unsafe/native_decide).
- I read ALL 87 actual type/axiom reports in MY Checks.log (18029 bytes): every declaration
  depends only on [propext, Classical.choice, Quot.sound]. No other axioms appear.
- Load-bearing modules read in full (SourceEndpoint, Zeros, Series, Tail, BernsteinBounds,
  PolynomialCertificates, PointValues, EvaluationCertificates):
  - SourceClaim365454 : ∀ α, 0≤α → α≤1/2 → ∀ M, 0<M → ∀ x, 0≤x → x≤1 → 0 ≤ sourceKernel α M x.
    Literal source assertion; no hidden hypotheses. Witness α=2/5, M=2, x=47/50 is applied
    inside the ranges (norm_num/decide discharge the side conditions), so the negation is
    closed. (M ∈ ℕ vs 0<M: equivalent since K_{·,0} ≡ 1 ≥ 0 trivially.)
  - sourceKernel matches the published p.7 formula term-by-term, including the M=0 ≡ 1
    convention; sourceZero is the recursive sInf construction (0 → 0, n+1 → sInf of zeros
    strictly after sourceZero n); besselJ0 is the genuine defining tsum; real rpow is literal
    (Real.rpow lemmas, (x^(2/5))^5 = x^2 proved).
  - source_first_two_characterization proves IsLeast semantics for the USED indices 1 and 2
    (not a surrogate sequence): source_first_two_zero_bounds pins sourceZero 1, 2 into the
    exact rational intervals via the csInf equations.
  - The five whole-interval bounds are kernel-checked: exact rational coefficient lists with
    decide +kernel bound checks, scaled identities by decide +kernel, and polynomial→
    Bernstein transforms by norm_num/ring. No sampling anywhere.
- Scope check: nu=0 suffices to refute the universal source assertion as analyzed in Gate 1.

## Gate 4 — NOVELTY: PASS (bounded screen; limits below). Not inherited from parent.

My own screens, all saved in this lane:
- Fresh OpenAlex (fetched by me): W7125473581 (published) and W4404305587 (preprint) each
  cited_by_count = 0. Treated as weak evidence only.
- Fresh MathDB 365454: open, zero activity (see Gate 1).
- arXiv API author query "Acosta Babb" (6 papers, latest 2503.18520 Mar 2025): no followup,
  no v2, no erratum/correction to 2410.17681.
- Multi-angle web searches (DuckDuckGo provider; Exa was rate-limited 429): no refutation,
  counterexample, or discussion of the conjecture's truth value found; author's related
  papers (2022/2023/2024) are on different problems.
- Local registries read-only: trureturing @f8ffe9ed02 (no Bessel–Fourier Fejér kernel
  positivity/negation entry; only tangential Fejér-near-collision zero-repulsion and
  Fourier-core blueprints) and cem @dbf6737 (no match).
- Classical subsumption screen on primary bodies (root's prior-body lane
  parent-bessel-prior-r24, IA copies MD5-matched to metadata; I independently read):
  - Watson 1922 §18.5–18.54: I visually read p.607 eq. (2) — the Riesz kernel is
    T_n(t,x|R) = Σ_{m<=n} (1 − j_m/A_n) · 2 J_nu(j_m x) J_nu(j_m t)/J_{nu+1}(j_m)^2.
    I confirm root's corrected weight (1 − j_m/A_n), not the squared weight. Different
    weights, two-variable normalized product, no j^alpha power; §18.54 is limiting/Cesaro
    comparison — NOT the source's finite modified Fejér kernel. No overlap.
  - Young 1920 (PLMS s2-18, 163–200): I visually read printed pp.171 (§5–7: coefficient
    decay k^{-s}A_r → 0 and Cesaro connection) and p.191 (§31–33: upper/lower functions and
    partial-sum differences tending uniformly to zero) plus OCR of the full article —
    asymptotic/convergence results only; no finite j_r^alpha kernel sign statement.
  - Classical Fourier Fejér kernel positivity concerns integer frequencies and different
    coefficients; it does not transfer. Logically, any classical theorem implying
    nonnegativity of this kernel at our witness would be false, so no true classical result
    can subsume the refutation; the only possible overlap would be an explicit prior
    computation of this kernel, which none of the screens found.
- Limits: no MathSciNet/zbMATH access; S2 root query 429 not retried by me; screen is
  bounded — no claim of global absence is made.

## Gate 5 — SUBSTANTIVE ELIGIBILITY: PASS (my own decision)

Strongest objections, tested honestly:
1. "Elementary once seen": the two-term computation is elementary in technique, but the
   result is a new mathematical fact — the first disproof of a specific open conjecture
   stated in a 2024 thesis/preprint and a 2026 published paper, unrefuted on MathDB with
   zero citers. It is not a corollary, wording, normalization, endpoint, or parameter-domain
   fix: the published statement retains the same range and is false as stated. Eligible.
2. "Small-M": M=2 is inside the explicit quantifier ("for all M ∈ N"). The source's own
   figures cover only M ≥ 10 at α=1/2, so the conjecture as written is not restricted to
   large M. My independent numeric scan shows the stated conjecture also fails at other
   parameters (e.g. α=1/2, M=10 dips to ≈ −0.0046 near x≈0.97; tiny dips invisible in the
   author's y-range-5 plots) — so M=2 is not an isolated artifact excluded by intent, and
   the small negative dips explain why the author's simulations suggested positivity. The
   failure is real, though shallow; the certified bound −1/500 is honest about magnitude.
3. "Plot error": the conjecture's text is unambiguous; the kernel is defined explicitly
   (p.7) and the witness point is strictly interior (α=0.4 ∈ (0,1/2), x=0.94 ∈ (0,1)).
   No reading of the source rescues positivity at the witness.
4. "Classical subsumer": ruled out on primary-body evidence (Gate 4) and by the logical
   point above.
No decisive obstacle. ONE outcome counted; the half-power witness is mathematical-only,
absent from the manuscript, and receives no credit; no slow-decay/conditional claim is made.

## Gate 6 — MANUSCRIPT: PASS

- Rendered and visually read ALL 3 pages of paper.pdf from my frozen byte copy
  (paper-render/page-{1,2,3}.png).
- Kernel display (1) matches published p.7 and Lean sourceKernel. Theorem 1 matches
  source_kernel_interior_negative. Attribution: [1] JMAA 559 (2026) 130440 doi correct;
  [2] arXiv:2410.17681v1 correct; "published discussion fixes Bessel order zero" is accurate.
- Table: all five rows match the Lean bounds and my independent Bernstein verification,
  including exact interval endpoints (9/4, 4761/625=5.5200^2/4, 3047150401/4e8=5.5201^2/4,
  4990150881/3906250000 and 1277584871809/10^12 = (c·2.4048/2.4049)^2/4,
  10517049/1562500 and 6731155235809/10^12). Bernstein formula (3) is the standard exact
  conversion and matches my implementation and Lean bernsteinSum_scaled.
- Zero-identification paragraph (4)–(5) matches Zeros.lean case analysis; tail displays (2)
  match Series_error/normalizedDerivative_error; final fraction −653867/300000000 < −1/500
  verified by hand and by my exact checker.
- Formal-scope paragraph: 87 declarations/8 modules, endpoint name, mathlib revision
  d13f23b723b8a846827a245b89c10fc7d3f11612 (matches pins.json), standard-3 axioms, credit-0
  and pending-gates framing, no priority claim, slow-decay conjectures explicitly undecided.
- Quantifier wording: "M ≥ 1" vs source "M ∈ N" — equivalent (K_{·,0} ≡ 1 trivially ≥ 0);
  formalization uses 0 < M. Not a distortion.

## Minor non-blocking blemishes

- bessel-exact-certificate.json carries a stale unrelated field
  "public_prior_checks": "Faà di Bruno cubic discriminant and elliptic antiderivative
  verified" — a provenance artifact from the certificate generator; no mathematical impact.
- Manuscript page-2 text "on [0,9/4]" renders with a visually tight comma in the PNG; the
  TeX source is correct ($[0,9/4]$).

## Verdict

All six gates PASS. No decisive objection. The candidate is eligible to proceed to the
parent's deterministic archive extraction and final replay; acceptance itself remains with
the root. Access limits and non-absence caveats are recorded above.

## What I actually read/checked (binding)

- 56/56 candidate files hashed and copied before work; re-verified 56/56 after work
  (candidate untouched; no git/staging/shared/ledger/count edits by this review).
- Full text: PROOF.md, FORMAL-CHECKPOINT.md, REVIEW-CHECKPOINT.md, main.tex, candidate.json,
  provenance.json, pins.json, verify_candidate.py, all 8 Lean modules (full reads),
  bessel-exact-certificate.json (key fields), published/arxiv/thesis txt extracts,
  MathDB record, OpenAlex responses, registry greps.
- Visual reads: published p7, p11; arXiv p10; paper.pdf pages 1–3; Watson p607;
  Young pp171, 191.
- Executed: my-math-check.py (all PASS, incl. mpmath cross-check), fresh isolated Lean
  replay (PASS, receipt byte-identical to parent87), forbidden-token scans, kernel scans.
