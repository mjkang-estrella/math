# Preliminary adversarial review — root-mittag-modulus-r12 (Mittag-Leffler squared-modulus CM)

Reviewer: Pi GLM-5.3-Flash (thinking=high, standard speed), solo, no children, no git/stage/commits,
no writes outside this lane. Date: 2026-10-28 (UTC times in provenance.json).
Candidate: frozen root lane `root-mittag-modulus-r12` @ 2444a7c30250141e52a8a55395099405d1ad3057,
20 files bound by its `review-freeze.json`. Credit status unchanged by this review: candidate 0;
campaign additional 2/30, total 32/60 (not recounted here).

## 0. Freeze verification

All 19 content files were extracted from the frozen commit and SHA-256 match `review-freeze.json`
exactly (the 20th file is the manifest itself). Byte-copy kept at
`frozen-copy/` in this lane. Re-verified after all review work: parent `PROOF.md` 470d36cb…,
`sources/source-v1.pdf` 13fb00f6…, `review-freeze.json` 2035d035… unchanged.

## 1. What the candidate claims

Full source statement (Chorfi–Et-tahri–Maniar–Yamamoto, arXiv:2510.03600v1, Section 5,
Conjecture 3, Eq. (5.2), p. 23): for 0<α≤1/2,
f(t)=|E_{2α,1}(−t)|² + t·|E_{2α,1+α}(−t)|² is completely monotone (or at least log-convex) on t>0.
MathDB 370772 (open, solutions empty) matches verbatim. I verified from the frozen actual source
PDF/text: statement, range, "or at least log-convex" wording, the source's own remark that
t·|E_{2α,1+α}(−t)|² alone is not log-convex, and the source's key formula (2.14)
E_{α,1}(−it)=E_{2α,1}(−t²) − it·E_{2α,1+α}(−t²) — the candidate's even/odd identity is (2.14)
with sign/signature checked. Other conjectures (zeros on imaginary axis, ψ zeros) are not claimed.

## 2. Independent mathematical re-derivation (reviewer's own, before reading any check script)

Every step was re-derived by hand; the following attack vectors were tried and failed to break it.

1. Even/odd identity: E_a(i√t)=E_{2a,1}(−t)+i√t·E_{2a,1+a}(−t), all terms real for t>0, hence
   |E_a(i√t)|² equals the literal source expression (abs² = ordinary square, argument real).
   Equivalently g(u)=E_a(iu)E_a(−iu) is even entire, so t↦g(√t) is entire. Cross-checked against
   the source's own (2.14). Exact for all real a>0 — no rational restriction.
2. Half-normal cf: H=|N(0,2)| has EHⁿ=n!/Γ(1+n/2), so its mgf is E_{1/2}(z); cf
   e^{−z²}(1+i·erfi(z)) re-derived by direct quadrature of the density (check A) and by the
   Dawson-integral identity ∫₀^∞ e^{−u²}sin(2zu)du=(√π/2)e^{−z²}erfi(z).
3. Angular kernel (2), unequal scales: erfi product = (4t/π)∫∫_rectangle e^{t(u²+z²)}; polar
   radial cut at R(θ)=min(√v/cosθ, √w/sinθ) with the switch exactly at θ₀=atan√(w/v);
   ∫₀^R r·e^{−t(S−r²)}dr=(e^{−t(S−R²)}−e^{−tS})/(2t); the e^{−tS} term cancels against the 1 in
   K. L≥0 because cos²θ≥v/S or sin²θ>w/S (their sum is 1). Verified by 2-D rectangle
   quadrature (independent of the root's 1-D angular quadrature) at unequal/extreme scales and
   t∈{0.001,…,80}; K∈(0,1], K(v,w,0)=1.
4. Finite-product construction: E Y_k^q=(k+βq)/(k+q) re-integrated directly from the stated
   two-part law for an irrational β (check C). Euler limit (5) and monotonicity ratio
   (1+1/N)^d ≥ 1+d/(N+1) (log(1+1/N)≥1/(N+1)) with exact gap d·βq/(N+1)≥0 — the algebra is
   exact, re-verified symbolically and numerically at irrational β via literal products up to
   N=4000 (check F), including q=0 and β=1 endpoints.
5. Moment domination and convergence: EX_Nⁿ/n!=R_N(n/2)/Γ(1+n/2) ≤ 1/Γ(1+an); Tonelli on the
   positive series gives E e^{rX_N} ≤ E_a(r); the bound Σ|z|ⁿ/Γ(1+an) is an entire majorant, so
   M_N(z)→E_a(z) pointwise and locally uniformly without any tightness/stable-law assumption.
   I specifically probed the three places such arguments usually hide a gap — (i) equality of the
   mgf with its Taylor series (justified by Tonelli, X_N≥0), (ii) complex z (reduce to Re z),
   (iii) the pass-to-the-limit in finite differences (finite sum of pointwise limits; the RHS of
   (10) is never evaluated). No gap found.
6. F_N=|M_N(i√t)|²=E K(V_N,W_N,t): φ_{A−B}=φ_A·conj(φ_B) for iid scales; conditioning on
   (V_N,W_N) and using step 3. Imaginary parts cancel by the real-kernel identity itself, not by
   an uncontrolled complex estimate.
7. Finite differences: (−1)^k Δ_h^k e^{−tL}=e^{−tL}(1−e^{−hL})^k ≥ 0; linear expectation; then
   h→0 on the entire limit f. Bernstein's characterization (classical, generic) is the only
   external theorem. The conclusion is exactly the source's own CM definition ((−1)ⁿf⁽ⁿ⁾(t)≥0,
   t>0), and proves the stronger CM option, hence a fortiori log-convexity.
8. Range check: the mechanism needs β=2a∈(0,1], i.e. exactly a∈(0,1/2] — neither more nor less
   than the conjecture's range. Endpoint a=1/2 (β=1, deterministic Y_k) verified separately via
   the closed form e^{−2t}(1+erfi(√t)²) and mpmath derivatives up to t=60 (check E2).

## 3. Reviewer's independent numerical checker (different routes from the root's)

`independent_checks.py` (sha256 40d14bc6…): A half-normal cf by direct quadrature; B angular
kernel via **2-D rectangle** quadrature (root used 1-D angular); C literal two-part-law moments at
irrational β=0.413753917…; D **finite-difference signs of F_N computed purely from the series
|M_N(i√t)|² without ever invoking the angular kernel** — this independently validates the
steps 3–4 machinery; E signs of (−1)^k f_a^{(k)}(t) for the literal source function via this
reviewer's own coefficient formula c_j=Σ_{j'=−j}^{j}(−1)^{j'}/[Γ(a(j+j')+1)Γ(a(j−j')+1)]
(cross-checked in G against the direct series product), with adaptive precision and truncation;
E2 endpoint a=1/2 closed-form derivatives; F Euler limit/monotonicity at irrational β.

Result: **PASS, 267/267 checks, 0 failures** (`independent-checks.json`, sha256 194db7aa…).
Max RSS 27 MB, wall 234 s (resource-bound compliant). 9 cases skipped for computational
infeasibility (documented in the JSON, e.g. a=0.25,t=20 needs ~10³⁴⁷-digit intermediate
precision; a=0.02,t=1.05,k≥4 needs J>6000) — these ranges are covered analytically by the proof,
not numerically. Root's own diagnostics (25 angular, 36 rational-Γ moment, 15 even/odd,
55 Taylor-coefficient, 240 Euler-product) re-read; all are necessary-condition diagnostics, none
constitutes proof; my E-check is strictly stronger than the root's Taylor-coefficient check
(actual derivative signs at positive t, not just c_j>0).

## 4. Per-gate verdicts

### SOURCE — HOLD (arXiv statement PASS; journal version-of-record equivalence OPEN)
- PASS component: Conjecture 3 / Eq. (5.2) / range 0<α≤1/2 / "completely monotone (or at least
  log-convex) for t>0" verified from the actual arXiv v1 PDF (frozen; p. 23 rendered and read;
  text extraction consistent). MathDB 370772 record matches verbatim; status "open", solutions []
  (fact, not novelty evidence). Crossref confirms VoR: CNSNS 157 (2026) 109758, PII
  S100757042600119X, June 2026 — matches the candidate's corrected record; the root's discarded
  wrong-PII guess was not used as evidence.
- OPEN component: the journal VoR body was not read. ScienceDirect returns HTTP 403 (respected;
  no bypass, no accounts, no challenges defeated). The Elsevier TDM API endpoints listed by
  Crossref require entitlement I do not have. OpenAlex lists a submitted-version handle and the
  arXiv version; neither was confirmed to be the published conjecture text. Mitigating fresh
  evidence (obtained this review): the same authors' follow-up arXiv:2603.16726 (submitted
  2026-03-17) cites "Conjecture 3 in [15]" as **open** and explicitly designs its proofs to
  avoid complete monotonicity at imaginary argument — strong evidence the VoR did not silently
  resolve it — but the VoR body itself remains unread, so this stays HOLD, not PASS.
- No v2 of 2510.03600 was found; v1-only status consistent with the root's record.

### MATH — PASS
Independently re-derived end to end; 267 independent numerical diagnostics with deliberately
different routes, all passing; no false-positive kernel, no moment-monotonicity error, no
convergence gap, no parameter/sign/scope pitfall found. Strongest objections I raised and
resolved: (i) the mgf/Taylor-series equality for X_N (Tonelli, X_N≥0 — sound); (ii) hidden
dependence of the mixture property on the kernel identity (eliminated by route D, which never
uses it); (iii) cancellation-driven false negatives in my own first checker run (artifact of my
harness, fixed with adaptive precision — recorded, not hidden); (iv) whether the limit passage
needs tightness or a stable-law existence theorem (it does not — the root's construction is
pointwise-moment domination, and this is its main strength); (v) endpoint and degenerate cases
(q=0, β=1, a=1/2, t=0) all verified. Numerical evidence remains diagnostic, not proof; the
analytic argument stands on its own.

### NOVELTY — HOLD
No exact published instance of CM of t↦|E_a(i√t)|² was located. Specifically checked:
- Banderier–Kuba–Wallner, AAP 34(5) 2024, DOI 10.1214/24-AAP2076 (public arXiv 2103.03751 v2
  read this review): the M-Wright/ML law is their Definition 3.8 (mgf E_α(t)); **no**
  characteristic function at imaginary argument, **no** squared modulus, **no** CM-of-modulus,
  **no** Gaussian-scale-mixture/angular-kernel content. Their only total-monotonicity mention
  cites Górska et al. for E_{γ′,α′,β′}(−t) at negative real argument. The task brief's
  "Example 3.10 is ours" does not match the arXiv v2 numbering (3.10 is the Beta-distribution
  definition); regardless, nothing in the paper subsumes the candidate. Not a subsumer.
- Korolev-line mixture papers (arXiv 1506.02778 etc.): their "Mittag-Leffler distribution" is
  the Pillai-type heavy-tailed law with Laplace transform 1/(1+s^α) — the *other* ML — and their
  normal scale mixtures mix in the opposite direction (Linnik as N-scale mixture with ML
  mixing). Definition verified before concluding: not a subsumer.
- Garrappa–Gerhold–Popolizio–Simon, JMAA 551 (2025) 129588: |E_{α,β}(z)| vs E_{α,β}(Re z)
  comparability; CM of E_{α,β}(−x) is an input, not the modulus-squared conclusion. Matches the
  root's reading: no modulus-squared CM found there either.
- Schoenberg connection (this reviewer's analysis): the conjecture is *equivalent* to the
  statement that the symmetrized M-Wright law X−X' (X iid M-Wright(a)) is radially positive
  definite in all dimensions, equivalently a Gaussian scale mixture — the candidate's proof
  establishes the Schoenberg criterion for it. I found **no published instance** of this fact,
  but a dedicated search for "M-Wright difference is a Gaussian scale mixture" type theorems
  was bounded; a referee-produced such theorem would make the result an immediate instance.
- Access limits: Semantic Scholar citations API returned 429 (respected, not retried);
  MathSciNet not accessible (no entitlement); local registry clones for this target were not
  found (grep hits belong to other campaigns' lanes and were not reused as evidence).
  MathDB/citer sweeps bounded to the queries logged in provenance.json.
No located-exact-result is not a PASS; novelty remains open at HOLD.

### SUBSTANTIVE — HOLD (eligible; leaning PASS, not asserting PASS)
The full-parameter mechanism — elementary atom+Beta(k,1) finite products giving monotone moment
bounds that dominate an entire majorant, plus the exact angular Laplace kernel, plus the
finite-difference passage — is not supplied by any located published mixture-closure theorem, and
it covers the exact asked range 0<a≤1/2 with no parameter correction or typo repair. The source
authors themselves, as of 2026-03, still treat the statement as open and design around it. That
is real evidence of non-triviality. But the ingredients are individually classical and
uncredited, and the decisive question (does an established GSM/radial-PD theorem for the
symmetrized M-Wright law exist?) is exactly the unresolved novelty gate; "elementary once seen"
is not an automatic FAIL here, and "no hit found" alone is not eligibility. Decision: HOLD until
the journal-body comparison and the remaining bounded novelty scopes close. Not forced by any
precedent; this is an independent decision.

### FORMAL — NOT ASSESSED (no full endpoint exists)
Pinned Lean 4.34.1 / mathlib d13f23b723b: I could not re-verify the absence claim by source grep
(local mathlib cache holds only .ltar olean archives — access limit recorded); the claim is
consistent with mathlib's known coverage. No Lean work was started. If the candidate proceeds,
the required bridges are, precisely: (1) ML/Wright function definition and entire-convergence
(Stirling bound) — none in mathlib; (2) the two-part law as a finite measure and its moment
formula (mathlib Beta/Gamma integrals plausibly usable); (3) the Euler Γ limit and the exact
monotonicity ratio inequality; (4) the half-normal Gaussian integral identity (3) and the 2-D
polar-coordinate rectangle identity (2); (5) complex moment/mgf series equality via dominated
summation; (6) finite-difference binomial lemma and the h→0 derivative passage on an entire
function; (7) Bernstein characterization or a direct CM-to-Laplace construction. An assumed
abstract mixture lemma or an abstract-CM surrogate is not a full certificate. No formal PASS or
count is given.

## 5. Strongest objection (full strength)

The entire result rests on one uncredited classical observation: the half-normal cross-scale
kernel (2) is a probability-measure Laplace mixture, and everything else is bookkeeping. If any
published theorem already states — or makes immediate — that the symmetrized M-Wright law is a
Gaussian scale mixture (equivalently, by Schoenberg's 1938 criterion, that t↦|E_a(i√t)|² is
completely monotone), the candidate collapses to a routine instance with no remaining content,
and the correct disposition becomes subsumption, not credit. The root itself flags this gate; I
could not close it because the relevant search scopes (journal VoR body, MathSciNet, Semantic
Scholar citations after 429, formal registries) were partially inaccessible within this review's
bounded budget. Second strongest: the VoR could differ from arXiv v1 (amended conjecture,
withdrawn, or resolved in proof), and until the publisher body is legitimately read, SOURCE stays
HOLD despite the mitigating 2603.16726 evidence.

## 6. Remaining gaps to acceptance (if root pursues)

1. Legitimate read of the CNSNS VoR conjecture section (or explicit confirmation v1 text is
   unchanged), without paywall/challenge bypass.
2. Bounded closure of the GSM/radial-PD M-Wright prior-art scope (MathSciNet, citation graph
   once rate limits permit, registries by actual record scope).
3. Full literal Lean endpoint with the seven bridges listed in §FORMAL — none exists today.
4. If surviving: paper + fresh strict replay per campaign rules.

No manuscript, acceptance decision, or count is made or implied by this review.
