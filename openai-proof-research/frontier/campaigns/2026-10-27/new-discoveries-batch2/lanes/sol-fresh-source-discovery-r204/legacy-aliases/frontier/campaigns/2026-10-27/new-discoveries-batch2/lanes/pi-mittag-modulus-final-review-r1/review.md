# Independent FINAL review — root-mittag-complete-r1 (new rational-kernel certificate + manuscript)

Reviewer: Pi GLM-5.3-Flash (thinking=high, standard/default speed), SOLO, no children, no
git operations, no writes outside this lane. Review date: 2026-10-28 (UTC stamps in
provenance.json). Candidate: frozen lane `root-mittag-complete-r1` @
ffde45206cbb9f8ff7d11db026b31c6e331372b2, `review-core-hashes.json` binding 65 paths
(MANIFEST.json itself outside its own hash map). Credit status unchanged by this review:
candidate 0; batch2 additional 2/30; total 32/60 (not recounted).

This is a NEW independent full final review of the NEW simplified 1D rational-kernel
formal route and the 3-page manuscript. It is NOT a continuation or ratification of the
included preliminary report (which reviewed the OLD frozen root-mittag-modulus-r12
polar/ordinary proof and issued a formal NOT-ASSESSED verdict); its outdated formal gap is
not inherited, and its REAL source/novelty/substantive holds are re-litigated here at full
strength, not silently cleared.

## 0. FREEZE — PASS

All 65 paths bound by `review-core-hashes.json` were extracted from the immutable git blob
`ffde45206cbb9f8ff7d11db026b31c6e331372b2` and SHA-256 verified: **65/65 exact** (0
mismatches, 0 missing). The frozen `review-core-hashes.json` in the worktree is byte-identical
to the frozen blob (c829c9d5…). My own byte-copy kept at `frozen-copy/` in this lane; all
review work (replay, checks, page renders) ran on that copy. `MANIFEST.json` extracted
separately (d1e66890…). Full detail: `frozen-copy-verification.json` (80390699…).

## 1. What the candidate is

Literal source statement (Chorfi–Et-tahri–Maniar–Yamamoto, arXiv:2510.03600v1 p.23,
Conjecture 3, Eq. (5.2); MathDB 370772): for 0<a≤1/2,
f_a(t)=|E_{2a,1}(−t)|²+t·|E_{2a,1+a}(−t)|² is completely monotone (or at least log-convex)
for t>0, with E_{ρ,β} the genuine convergent Gamma-denominator series.

The closed Lean endpoint is `MittagModulus.source_conjecture_370772 :
MittagModulus.SourceClaim370772` with NO residual premises. `SourceClaim370772 :=
∀ a, 0<a→a≤1/2 → CompletelyMonotonePositive (sourceExpression a)` where
`sourceExpression a t = normSq (mittagLeffler (2a) 1 (−t)) + t·normSq (mittagLeffler (2a)
(1+a) (−t))` is the literal two-series expression, and `CompletelyMonotonePositive`
quantifies C^∞ on (0,∞) and all alternating derivative signs `0 ≤ (−1)^k·f^{(k)}(t)`,
k∈ℕ. The old conditional lemmas (`sourceClaim_of_positiveMixedApprox`,
`sourceClaim_of_halfCross_positive`) still exist but are DISCHARGED: the terminal
`source_conjecture_370772` is proved directly from `halfCross_positive` via
`KernelIdentification`, and I re-checked the whole dependency chain module by module.

## 2. FORMAL — PASS (own fresh replay)

I ran `python3 verify_candidate.py` myself, in my own byte-copy, in a fresh source-only
tempdir (no olean copying), with `warningAsError=true`, absolute pinned tool and packages:

- **PASS: 17 modules, 155 unique named public declarations**, all module compile logs empty
  (exit 0, no output), endpoint check printed
  `MittagModulus.source_conjecture_370772 : MittagModulus.SourceClaim370772`.
- `#print axioms` on all 155 declarations: **only propext, Classical.choice, Quot.sound**
  (156 report lines; `source_conjecture_370772` reported twice by the Checks.lean tail
  re-#check; set equality with the 155 names asserted by the script and re-verified by me).
  No sorry/admit/axiom/unsafe/native_decide (regex-asserted per module; I re-read every
  module source myself).
- My `verification/Checks.log` is **byte-identical** (aa7a1156…) to root's frozen
  `verification/Checks.log`, and my `verification/audit.json` is byte-identical to root's
  frozen audit. Pins asserted: lean binary sha256 e8baaa71…, version string exact, all 8
  packages at pinned revisions with clean `git diff` trees, Mathlib at d13f23b723b8…
- I read the actual mathematical content of all modules (not just type reports): series
  convergence via residue-class splitting + eventual geometric Gamma-ratio bound
  (SeriesConvergence), literal even/odd identity and sourceExpression (SourceDefs),
  real/complex analyticity (RealAnalytic/ComplexAnalytic), exact B_n moments and the two
  half-order identities from genuine termwise integration under a uniform e^{|x|} majorant
  (HalfIntegral), the ODE identification of the closed form with the rational Laplace
  integral incl. arctan initial value and both zero scales (RationalKernel/
  KernelIdentification/CompactParameter), the atom+Beta(k+1,1) normalized operators with
  the extra (N+1)-factor product, monotone ratio `((N+1)/N)^d·(N+2+βq)/(N+2+q) ≥ 1` with
  the exact gap d(1+βq)/(N+1) (EulerMoments), genuine finite-average identities and
  dominated-convergence passages (BetaAverages/AveragingRepresentation/SquaredAverage/
  Approximation/NormBridge), and the finite-difference-to-derivative induction
  (DifferenceCriterion). No hidden assumptions, no abstract mixture-existence premise, no
  unproved interface remains.

## 3. MATH — PASS (own independent diagnostic code)

`independent_checks.py` (fefb409c…), results `independent-checks.json` (4baed3e2…):
**133/133 checks pass, 0 failures**, ~57 s wall, small memory. Routes are deliberately
different from root's diagnostics and from the preliminary polar-route checker:

- A. Literal series vs closed form: E_{1/2,1}(ir)=e^{−r²}(1+2ir/√π·I(r²)) and
  ∫₀¹e^{−x(1−u²)}du=(√π/2)E_{1,3/2}(−x), exact to ≤1e-27 (mpmath dps 40).
- B. The NEW kernel identity three ways — literal series product, closed product form
  e^{−(v+w)t}[1+4t√(vw)/π·I(vt)I(wt)], and the rational 1-D integral J — agree to ≤1e-12
  relative across extreme scale ratios (1e-4..100), long times (t=80), near-degenerate and
  equal scales; zero scales equal e^{−(v+w)t} from the literal series.
- C. Both sides of the ODE identification P'+SP = J'+SJ =
  (2√(vw)/π)[e^{−wt}I(wt)+e^{−vt}I(vt)] with J(0)=1 (residuals at central-difference
  truncation level, and P, J residuals agree to machine precision).
- D. T_k x^q=(k+1+βq)/(k+1+q) x^q by adaptive quadrature at irrational β=0.413753917…;
  R_N(q) literal products: monotone in N, bounded by Γ(1+q)/Γ(1+βq), and converging with
  the exact O(1/N) rate (relative errors 8.6e-2, 1.0e-2, 1.2e-3, 1.2e-4 at
  N=10,100,1000,10000 for β=0.7,q=1.3 — trend verified, exact at β=1 and q=0).
- E. |M_N(i√t)|² == double average of the closed-form kernel, verified via an independent
  SUBSET-DECOMPOSITION of the composed atom+Beta mixture (equivalently, the product-form
  factorization K=A(v)A(w)+√v√w·C(v)C(w) with smooth factors and an s² substitution that
  removes the √-kink), for (a,N,t) ∈ {0.35,0.25,0.5,0.2}×{0,1,2}×{0.3..2.2}, all ≤1e-9
  relative. [My first attempt with naive nested Gauss–Legendre showed an 8.7e-6 mismatch —
  diagnosed as pure quadrature error on the √v endpoint kink (error decays ~n^{-3} with
  nodes), not a math issue; the restructured check is exact to 1e-9+.]
- F. Mixed lower differences of the actual squared approximants ≥ 0 computed PURELY from
  the series |M_N(i√t)|² (never invoking the kernel), multiple step tuples.
- G. Literal source expression f_a via the genuine even/odd series: coefficient signs
  (−1)^j d_j ≥ 0 for j ≤ 120/160 at a∈{0.2,0.35,0.5} (d_j = Σ_{s=−j..j} (−1)^s/[Γ(a(j+s)+1)
  Γ(a(j−s)+1)]) and actual derivative signs (−1)^k f_a^{(k)}(t) ≥ 0 for k∈{1,2,3,5} at
  a∈{0.05,0.2,0.35,0.5}, t∈{0.2..4} (a=0.05 restricted to t≤1 for series-convergence
  feasibility of my harness — covered analytically by the proof).
- H. Endpoint a=1/2: |E_{1/2}(i√t)|² = |e^{−t}(1+erf(i√t))|² exact.

Numerical work is diagnostic only; the proof stands on the Lean certificate. All failures I
encountered during development were my own harness artifacts (float input r*r, a sign typo,
over-tight tolerances, GL quadrature at the kink) — each diagnosed and documented, none a
defect of the candidate.

## 4. SOURCE — HOLD (arXiv v1 statement verified live; journal VoR body UNREAD)

- **PASS component.** The frozen `sources/source-v1.pdf` (13fb00f6…) matches a fresh live
  download of https://arxiv.org/pdf/2510.03600v1 **byte-for-byte** (2026-10-28). I read the
  actual conjecture text from the extracted source: Conjecture 3, p. 23, Eq. (5.2), exact
  range 0<α≤1/2, "is completely monotone (or at least log-convex) for t>0", the source's
  own remark that the two summands alone do not suffice (t·|E_{2α,1+α}(−t)|² not
  log-convex), and key formula (2.14). MathDB 370772 re-fetched live: status "open",
  solutions [], record **byte-identical** to the frozen copy (646494d8…).
- **OPEN component (kept at HOLD, not silently cleared).** The published VoR
  CNSNS 157 (2026) 109758, PII S100757042600119X (Crossref re-verified today: volume 157,
  article 109758, June 2026) remains materially unread. New lawful routes attempted this
  round, all exhausted: OpenAlex and Unpaywall list NO open published version (only the
  arXiv submittedVersion and a submittedVersion handle); the handle
  hdl.handle.net/20.500.12628/29535 (Zonguldak Bülent Ecevit repository) does not resolve
  ("Cannot Connect to Server", and it would be a submittedVersion anyway); ScienceDirect
  returns 403 on a single direct check (respected; no retry loop, no challenge bypass, no
  credentials); no arXiv v2 exists. No fabricated body-read.
- **Strong mitigation (obtained and read this review).** The same authors' follow-up
  arXiv:2603.16726v1 (submitted 2026-03-17) — body read from the arXiv HTML — states in its
  Section 4.1 remark: "the complete monotonicity of the function |E_{α,1}(−is^α)|, for
  s>0, seems to be difficult; we refer to Conjecture 3 in [15] for more details. Thus, we
  needed to modify the proof without using the complete monotonicity." This is after the
  journal acceptance/publication window (Crossref issue June 2026; OpenAlex online date
  2026-01-16) and is strong evidence the VoR did not silently resolve or remove the
  conjecture. Mitigation is not equivalence: SOURCE stays HOLD until a lawful VoR body
  read, per the review charter.

## 5. NOVELTY-SUBSTANTIVE — HOLD (no subsumer located; eligibility for root to adjudicate)

Bounded screens performed this round (all keyless/lawful; limits recorded):

- **Banderier–Kuba–Wallner** (my own body read of arXiv:2103.03751v2 PDF): the
  M-Wright/Mittag-Leffler law is **Example 3.10** (the task brief's "Def 3.8" does not
  match v2 numbering; 3.8 is a Remark on the tilt operator). Its mgf is E_α(x), special
  case M_{1/2} = half-normal |N(0,2)| (their Example 3.17 is mixed-Poisson half-normal).
  Grep of the full text: **no** "scale mixture", **no** "symmetr*", no characteristic
  function at imaginary argument, no squared modulus, no difference-of-iid statement.
  Their only total-monotonicity content concerns E_{γ′,α′,β′}(−t) at negative real
  argument. **Not a subsumer.**
- **Cahoy et al. arXiv:1705.01216** (body read): three-parameter one-sided and *symmetric
  bimodal* M-Wright families for inference; the symmetric class is the random-sign ±X
  symmetrization (cf Re E_a(iu)=E_{2a}(−u²)), not the difference X−X′. Not a subsumer.
- **Citation graph** (Semantic Scholar, one successful query then 429 respected): the VoR
  DOI has exactly 2 citing works — arXiv:2602.07514 (averaged controllability; body
  checked: no conjecture/CM content, uses asymptotic expansions) and a 2026
  stability/inverse-problems paper with no arXiv id and no accessible body (limit
  recorded). Neither subsumes.
- **arXiv metadata sweeps** (export API): "M-Wright"+"scale mixture" → 0 hits;
  "Wright function"+"completely monotone"+"modulus" → 0; "completely monotone"+"imaginary
  argument" → only the authors' own 2603.16726; "positive definite"+Wright+cf → 0.
  DuckDuckGo queries returned nothing closer than generic Schoenberg/Pólya and
  variance-gamma background. Exa rate-limited (429, respected); MathSciNet/zbMATH not
  accessible (no entitlement) — recorded limits, not absolute sweeps.
- **Routine-bridge angle attacked directly.** For iid X that are themselves Gaussian scale
  mixtures, X−X′ is trivially a GSM (product of completely monotone functions in u²), but
  the one-sided M-Wright(a) law is one-sided and is NOT itself a GSM, so that generic
  closure does not reach this object. I located no published theorem making the
  symmetrized difference of *half-normal-type one-sided scale-mixture* inputs a GSM, and
  no published instance of CM of t↦|E_a(i√t)|². An exact prior instance or a published
  two-step bridge (M-Wright-as-half-normal-scale-mixture + generic symmetrized-difference
  closure) would be decisive FAIL; none found within the bounded screen.
- **Substantive:** the new route is a genuine simplification with real content: an exact
  positive 1-D rational Laplace representation of the half-order cross kernel proved by a
  first-order ODE identity and arctan initial value (no polar geometry, no 2-D integrals),
  the actual normalized beta-atom operators with the extra (N+1)-factor Euler product
  (verified consistent with the Lean T_0..T_{N+1} indexing at scale (n+1)^{1−β} — no
  off-by-one between PROOF.md, manuscript and Lean), and a fully effective
  finite-difference passage. No stable-law existence, assumed Gaussian law, polar identity
  or Bernstein-representation surrogate is used anywhere. The exact asked range 0<a≤1/2 is
  covered with no parameter repair (endpoint a=1/2 handled separately in Lean and by my
  check H). The source authors themselves treat the statement as open as of 2026-03.

## 6. MANUSCRIPT — PASS

All 3 pages of paper.pdf rendered at 110 dpi and visually read (pages/page-*.png): no
overfull/underfull boxes, no undefined references, theorem/lemma numbering consistent.
Every displayed formula checked against the Lean sources and my independent checks,
including: Eq. (1) half-order identities, Eq. (2) closed kernel, Eq. (3) rational kernel,
the T_k operator with k≥1 indexing, Eq. (4) R_N(q) with the N+1-factor product and scale
N^{1−β}, the monotonicity-ratio algebra with exact gap d(1+βq)/(N+1), the coefficient
domination 0≤R_N(n/2)/Γ(1+n/2)≤1/Γ(1+an), the mixed-difference formula, and the finite
difference → derivative induction. The status section is honest: no acceptance asserted,
credit 0, journal body not yet compared, no priority claim. Date October 28, 2026; single
reference correct (arXiv v1, Section 5, Conjecture 3, Eq. (5.2)).

## 7. Strongest objection (full strength)

The entire mathematical content rests on one observation: the half-order cross kernel
K(v,w,t)=e^{−(v+w)t}[1+4t√(vw)/π·I(vt)I(wt)] is a positive Laplace mixture of exponentials
— everything else is disciplined bookkeeping. If any published theorem already states (or
makes immediate by a routine two-step bridge) that the symmetrized difference of iid
one-sided M-Wright variables is a Gaussian scale mixture — equivalently, by Schoenberg
1938, that t↦|E_a(i√t)|² is completely monotone — the candidate collapses to a routine
instance and the correct disposition is subsumption, not credit. My bounded screen found no
such theorem and I showed the naive generic closure (difference of GSMs) does not reach
one-sided inputs, but the decisive scopes (MathSciNet/zbMATH, full citation graphs, the
VoR body, Exa after 429) were partially inaccessible. Second strongest: the VoR could still
differ from arXiv v1 (amended/withdrawn/resolved in proof); until a lawful publisher-body
read, SOURCE stays HOLD despite the strong 2603.16726 mitigation.

## 8. Exact remaining holds

1. **SOURCE/HOLD:** lawful read of the CNSNS 157 (2026) 109758 VoR conjecture section, or
   an authoritative equivalence statement; 403/entitlement gates respected, handle
   unresolvable, no arXiv v2, no OA published copy exists per OpenAlex/Unpaywall.
2. **NOVELTY-SUBSTANTIVE/HOLD:** bounded-only prior-art screen; unresolved decisive
   question is a published GSM/radial-PD theorem for the symmetrized one-sided M-Wright
   difference (or a published generic half-normal-scale-mixture symmetrization closure
   plus a published M-Wright subordination into it); the second citing work (no arXiv id)
   body unread; MathSciNet/zbMATH and Exa-based sweeps unavailable.

No acceptance, no count change, no ledger/shared edits, no publication. Candidate credit
remains 0; batch2 remains 2/30; total 32/60. Root adjudicates eligibility.
