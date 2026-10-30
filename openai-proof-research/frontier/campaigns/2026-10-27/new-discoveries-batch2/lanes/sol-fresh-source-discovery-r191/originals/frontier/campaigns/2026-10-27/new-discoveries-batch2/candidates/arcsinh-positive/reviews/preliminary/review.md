# Independent preliminary review: root-arcsinh-positive-r1 (frozen dcef9ead57)

Reviewer: Pi GLM-5.3-Flash-EXL3, thinking=high, standard speed. Solo; no children;
no git operations; no edits outside this lane. Work performed 2026-10-28.

## Verdict summary

| Gate | Verdict |
|---|---|
| SOURCE (exact target) | PASS |
| MATH (independent) | PASS |
| FORMAL (independent fresh replay + report read) | PASS |
| NOVELTY (bounded) | PASS, bounded (no worldwide-priority claim) |
| SUBSUMPTION (bounded) | PASS; all concrete bridges checked and closed |
| SUBSTANTIVE eligibility | PASS (adversarial objection weighed; see §6) |
| Paper / packet / final review | NOT ASSESSED — do not exist; no claim made |

Recommendation to parent: eligible to proceed to manuscript and final review.
No count, no ledger edit, no acceptance is issued or implied by this review.

## 1. Source gate — PASS

I independently extracted text from the candidate's frozen `sources/survey2019.pdf`
(SHA256 8ddfe433...303657, verified in the frozen copy before and after lane copy)
with my own `pdftotext` run (own/survey2019.txt):

- Title page: Li Yin, Li-Guo Huang, Yong-Li Wang and Xiu-Li Lin, *A survey for
  generalized trigonometric and hyperbolic functions*, J. Math. Inequalities
  13(3) (2019), 833–854, doi:10.7153/jmi-2019-13-58. The four-name attribution is
  correct; the old preliminary review's contrary attribution was an error.
- Eq (1.14), printed p.835: arcsinh_p(x) = ∫_0^x (1+t^p)^(-1/p) dt on [0,∞).
- Conjecture 5.1, printed p.847 (PDF page 15): "For x ∈ (0,1) fixed, the function
  p → arcsinh_p(x) is strictly concave on (1,∞)", with the Turán consequence
  arcsinh_p(x)^2 > arcsinh_{p-1}(x) arcsinh_{p+1}(x) for p>2 explicitly stated as
  "in particular" — so the concavity statement is the primary question.
- The survey attributes the origin to the Filomat 2015 Baricz–Bhayo–Vuorinen paper
  (its ref [6]); that paper's Conjecture 2.4 (read in the frozen
  filomat-published.txt, line 291) used all p>0 and is refuted at small p by the
  old uncredited witness. The survey's restated (1,∞) version is the surviving
  question. These are correctly separated by the candidate; this review does not
  re-credit the old witness or treat the candidate as a small-p correction.

Live MathDB 325512 refetched 2026-10-28: status open, empty solution/comment
arrays, statement is the original all-p>0 wording, "no resolution is reported in
the source". Empty arrays are not novelty evidence; the record is also not the
exact narrower target.

## 2. Math gate — PASS (independent)

I re-derived every identity by hand and re-verified exactly in sympy
(own/review_math_check.py, results own/review_math_check.json):

- ℓ = log f, ℓ_p = H(t^p)/p² with H(u)=log(1+u)−u log u/(1+u). Exact (sympy 0).
- H'(u) = −log u/(1+u)²; H(u) = −r log r −(1−r) log(1−r), r=u/(1+u) ∈ (0,1).
  Hence 0 < H ≤ H(1) = log 2. Exact (sympy 0).
- f_pp = f/p⁴[H(t^p)² − 2p·H(t^p) − p³(log t)²·t^p/(1+t^p)²]. Exact (sympy 0).
- For p > log2/2: H(t^p) ≤ log 2 < 2p, so H²−2pH < 0, and the last term ≤ 0, so
  f_pp < 0 for every t>0, p>log2/2 — strict pointwise concavity of the integrand.
  Note ℓ_pp < 0 holds for ALL p>0, but concavity of f needs ℓ_pp + ℓ_p² < 0,
  which is where 2p > H is genuinely used; the theorem is not trivally
  "log-concave ⇒ concave".
- Integration: integrands continuous on [0,x] for p>0 (at t=0 the integrand is 1);
  strict pointwise Jensen inequality on (0,x], equality only at t=0; the strict
  gap integrated against a positive-measure witness (t=x) gives strict concavity
  of A(p,x) on (log2/2,∞) for every x>0. No derivative-under-the-integral
  interchange is used. No optimality claim is made. Sound.
- The interval (log2/2,∞) ⊇ (1,∞) since log 2 < 2. The source conjecture follows.
- Independent numerics: 90/90 Jensen gaps A(pm,x)−mix > 0 on a grid with
  x ∈ {0.13,…,40} (including x>1) and p0 ∈ {0.4,…,30} (min gap 7.3e-32, at
  quadrature-noise scale); A_pp < 0 by central differences. Diagnostics only; the
  Lean certificate is the formal proof. The frozen check_proof.py's 3 exact
  symbolic identities, 36 second-derivative and 18 actual-integral midpoint
  diagnostics are consistent with my own runs.

No error found. The proof is complete, self-contained and correct as stated.

## 3. Formal gate — PASS (independent)

- All 38 files of review-hashes.json verified SHA256-identical in the candidate
  lane before copy and in my lane copy after copy (candidate-frozen/).
- Fresh own-copy strict replay `python3 verify_candidate.py` in my lane: PASS —
  5 modules, 19 declarations, warningAsError, empty module logs, only
  propext/Classical.choice/Quot.sound, pinned lean 4.34.1
  (e8baaa71…d5550) and mathlib d13f23b7…1612 with 8 dependency revisions
  re-verified by git rev-parse inside the script.
- I read the frozen Checks.log actual types for all 19 declarations and the two
  endpoints: `source_conjecture : SourceConjecture` closed, where
  `SourceConjecture = ∀ x, 0<x → x<1 → StrictConcaveOn ℝ (Ioi 1) (fun p ↦
  sourceArcsinh p x)` with `sourceArcsinh p x = ∫ t in 0..x, (1 + t^p)^(-(1/p))`
  — a literal `intervalIntegral` and literal `Real.rpow` powers
  (`rpow_def_of_pos`), no residual calculus hypothesis, no extra premises.
  Stronger endpoint `sourceArcsinh_strictConcaveOn` carries only `0 < x` on
  `Ioi (log 2/2)`.
- Inspection details: the t=0 endpoint is handled exactly (integrand equals 1
  there; strictness witnessed at t=x via
  `intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt`);
  `entropyExpression` is a genuine `Real.binEntropy` (proved equal, with
  `binEntropy_pos`/`binEntropy_le_log_two`); the diagonal-parameter effect enters
  through `hasDerivAt_entropy_exp` (chain rule through exp(a·q)), not by
  specializing a fixed-q statement. No `sorry/admit/axiom/unsafe/native_decide`
  (regex in script + my read of all five modules).
- The stronger all-x>0, p>log2/2 statement is proved for the literal integral, so
  the source endpoint is a two-line monotone-interval consequence.

## 4. Novelty gate — PASS, bounded

Independent screen (my own searches, not inheriting root's):

1. RACSAM 2025 (Deng–Peng–Zhong, doi:10.1007/s13398-025-01769-2): the full body
   is open access at Springer and I READ it (fetched 2026-10-28). It proves
   Theorem 1.1, the Wilker-type inequality p·sin_p(x)/x + tan_p(x)/x >
   px/sin_p(x) + x/tan_p(x), i.e. Open Problem 7.5 (Yin–Huang–Qi 2014) of the
   survey — NOT Conjecture 5.1. Cleared by actual body, not title.
2. 2026 successor, doi:10.1515/ms-2026-0304 (Mathematica Slovaca, Zhao): abstract
   states it is a (p,q)-extension of the same Yin et al. problem "recently solved
   by Deng, Peng and Zhong" and proves an inequality for (p,q)-generalized sine
   and tangent functions. Different problem; full De Gruyter body UNREAD
   (subscription). Recorded as a candid limit.
3. Darkunde–Ghodechor 2026 (DRNA Padova, vol 19, 22–30): full open-access PDF
   read. Its "conjectures of Yin et al. and Klén et al." are the monotonicity of
   ln(t·sin_p(t))/ln(cosh_p(t)) (p∈(1,2]) and two Klén ratio/bound conjectures —
   not arcsinh_p parameter concavity. Cleared by body.
4. Karp–Prilepkina 2015 (JMAA 421, frozen text read): proves p ↦ sin_p, cos_p,
   sinh_p, tanh_p (forward/inverse-function direction) log-convex/log-concave
   results; Corollary 3 log-convexity of sinh_p uses the kernel
   λ(p,t)=(1+t^p)^(-1/p) but the object is sinh_p(y), the inverse function — not
   A(p,x). Karp–Prilepkina 2024 (Mathematics 12:3383, frozen text read):
   Corollaries 1–4 and Theorem 4 are separate-parameter (p,q) statements
   (p fixed / q fixed); nothing diagonal; arXiv 2411.13442 v1 sole version
   confirmed on the live abstract page.
5. Filomat 2015 published body (frozen text, read): Theorem 2.6 proves separate
   concavity only; its proof even establishes integrand concavity in the first
   parameter with the OTHER fixed: "the integrand of arcsinh_{p,q}(x) is strictly
   concave with respect to p on (log 2,∞) for q > 0 and t ∈ (0,1)" (printed p.312).
   Setting q=p there is invalid — with q fixed, d/dp log(1+t^q) = 0, while on the
   diagonal the entropy term H(t^p) appears precisely from d/dp log(1+t^p) ≠ 0.
   See §5.
6. 18 OpenAlex citing works of the survey (frozen JSON enumerated): none is about
   parameter concavity of arcsinh_p; the closest titles were checked as in 1–5.
7. Targeted web searches (Exa, DuckDuckGo; see access log): no published
   resolution, no author followup proving Conjecture 5.1, no MathDB solution.
8. trureturing/count-ex-machina: not searched by content (not plausibly on-topic
   for a classical-analysis conjecture); noted as a limit, consistent with the
   bounded-screen standard.

No prior resolution of the exact surviving conjecture was found. This is a
bounded screen, not a worldwide-priority certification.

## 5. Subsumption gate — PASS; concrete bridges examined and closed

The task's strongest objections, each investigated to a conclusion:

(a) *Generic reciprocal-ℓp-norm concavity theorem.* f(p,t) = (1+t^p)^(-1/p) =
1/‖(1,t)‖_p, so a theorem "1/‖x‖_p is concave in p" would subsume the integrand
step. I closed this from two directions:
  - Such a general theorem is FALSE: I found and confirmed at 60-dps precision a
    probability vector q≈(0.201,0.309,0.184,0.208,0.098)/Σ with
    1/‖q‖_{pm} − mix = −2.50e-4 (p0=0.410, p1=1.096, λ=0.18). So no published
    all-dimensions theorem can exist, and no false theorem can be cited.
  - The nearest true generic statement, d²/dp² log‖q‖_p > 0 for nonnegative
    vectors (elementary: Σ q_i^p[(p·s_i)² + 2p·s_i + 2] with s_i=−log q_i ≥ 0;
    confirmed numerically, min +4e-21), gives only log-concavity of the
    reciprocal, and log-concavity does NOT imply concavity (f_pp = f(ℓ_pp+ℓ_p²)
    needs ℓ_p² < −ℓ_pp). So the log-convexity folklore cannot supply the result.
  - The two-point case is exactly the candidate's integrand theorem; I found no
    published two-point statement. The power-mean literature (e.g. "On
    (log-)convexity of power mean", AMI 42) proves M_p is log-CONCAVE for p≥0 —
    the opposite direction, and f = 2^(−1/p)/M_p(1,t) is not covered by it.
(b) *Filomat Theorem 2.6 as a bridge.* Separate p- and q-concavity of
arcsinh_{p,q} does not imply diagonal concavity: the mixed derivative is essential.
Concretely, Filomat's own integrand-p-concavity (fixed q) rests on
log(1+t^q)[log(1+t^q)−2p] < 0 with d/dp log(1+t^q)=0; on the diagonal the same
computation gains the term −p³(log t)²t^p/(1+t^p)² and the H(t^p) correction, and
the Filomat statement is not valid at q=p. No valid joint/mixed-derivative bridge
from Theorem 2.6 to the diagonal exists in that paper (I read its proof, p.312).
(c) *Karp–Prilepkina inverse-concavity bridge.* Their 2015/2024 results prove
log-CONVEXITY of the forward p ↦ sinh_{p,q}(y) (with the other parameter fixed)
and separate-parameter criteria for sin_{p,q}; none yields concavity of the
inverse-diagonal integral A(p,x). Directions and quantifiers checked in the
actual texts.
(d) *Turán shortcut.* Conjecture 5.1's "in particular" Turán inequality is
log-concavity of arcsinh_p in p, which is weaker than concavity; no published
proof of even that inequality for the single-parameter arcsinh_p was found
(Karp 2024's Turán-type statements are for the (p,q) forward functions).

No concrete subsuming result survives. The candidate's theorem is not a routine
corollary of any located established theorem.

## 6. Substantive eligibility — PASS (with candid caveat)

Adversarial case: "short classical binary-entropy/calculus proof; possibly
routine." Weighed:

- The result resolves a conjecture that its own source authors restated as open
  in 2019, that MathDB carries open with no resolution, and that no citing work
  resolves (§4). Under the campaign standard, a complete proof of a surviving
  open source conjecture is substantive; shortness is not an exclusion ground
  (cf. accepted outcome 23, a parameter-convexity threshold result).
- The routine-corollary exclusion requires an established theorem containing the
  needed content. None exists: the generic version is false (my dim-5
  counterexample), the log-convexity folklore is strictly weaker
  (log-concave ≠ concave), and the published separate-parameter concavities do
  not reach the diagonal. The candidate's entropy-term correction is exactly the
  new content separating the diagonal from the published separate case.
- Caveat recorded for the parent: the mathematical machinery is elementary
  (binary-entropy bound + one exact second-derivative identity + Jensen), and
  the same authors' school came within one line of the separate-parameter
  version in 2015. This is an eligibility judgment call, and I recommend
  eligible; it is not a priority or depth claim.
- One-family accounting is correct and consistently scoped: the entropy lemma,
  derivative identity, x>1 extension, old small-p witness, and the Turán
  consequence earn no separate credit; the old witness stays credit 0. The
  candidate does not conflate the new proof with re-crediting the old
  counterexample.
- Consistency with prior exclusions: unlike the Gamma #23-style exclusions and
  the 364606/338822-style immediate-corollary exclusions, here there is no
  known-result bridge; unlike 325512's old rejection, the domain correction was
  made by the source authors themselves in 2019, not by this candidate.

## 7. Scope honesty and limits

- Bounded novelty screen; no MathSciNet/zbMATH; Exa rate-limited (429) after two
  successful query batches — not repeated; Brave API unavailable; De Gruyter
  2026 body and any paywalled citing bodies unread; trureturing and similar Lean
  repositories not content-searched. No worldwide-priority claim is made or
  supported.
- The candidate's own PRIOR-ART-SCREEN.md correctly disclaims clearance; this
  review is the independent screen the candidate awaited.
- No manuscript exists; no paper/packet/final-review/acceptance gate is claimed
  here. Parent owns integration, counting, acceptance, staging and commits.

## 8. Access and provenance log

See provenance.json in this lane for exact URLs, hashes, commands and failures.
Key items: frozen copy hash-verified 38/38 before and after; fresh replay PASS;
Springer RACSAM full text fetched 2026-10-28 (open access); DRNA PDF fetched;
MathDB 325512 fetched live; Exa 429 respected; DOI 10.1007/s13398-025-01769-2
via doi.org returned HTTP 406 to the fetcher and was fetched via
link.springer.com instead (no paywall bypass; the article is freely readable).
