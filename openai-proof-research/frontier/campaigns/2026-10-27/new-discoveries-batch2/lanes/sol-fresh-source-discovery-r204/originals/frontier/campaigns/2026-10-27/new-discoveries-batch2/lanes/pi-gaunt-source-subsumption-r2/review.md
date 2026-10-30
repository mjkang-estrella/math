# Independent narrow review r2 — source access + classical-subsumption adjudication

Reviewer: pi GLM-5.3-Flash, thinking=high, SOLO. 28 October 2026 (completed 21:40 UTC).
Scope: the two held gates of frozen `root-gaunt-optimality-r3@c20af1d79a` (full 70-file
manifest): (P1) obtain/read the actual published Proc. AMS conjecture section, and (P2)
independently adjudicate classical subsumption / substantive eligibility at full strength.
No children, no git writes, no shared/candidate edits, no external messages, no counting,
no acceptance. All scripts memory-bounded; all frozen byte hashes verified before and after
(70/70 OK in the original lane and in my own byte-identical copy `own-copy/`; zero changes).
The completed `pi-gaunt-integral-final-review-r1` PASS on formal/math/manuscript/packet is
noted but NOT re-derived and does not clear source/novelty. I read the candidate's actual
`ORDINARY-PROOF.md`, `SOURCE-PRIOR.md`, `SUMMARY.md`, `main.tex`/`paper.pdf` (via the frozen
sources and render pages), the final review report, `root-gaunt-final-review-adoption-r1.md`,
`root-gaunt-access-followup-r2/ACCESS-NEXT.md`, the batch/ancestor AGENTS.md, ledger.json and
prior-campaign-context.json, and adjudicated the actual source statement myself (arXiv v2
pp. 6–7, Conjecture 2.4 + Remark 2.5, read from the frozen extraction and page render).

## P1. Published-body access — all lawful routes exhausted this turn; HOLD retained

Route log (2026-10-28, all real HTTP statuses; no challenge bypass, no login, no captcha
solving; each blocked class stopped after first failure, no loops):

1. **AMS accepted-manuscript PDF** `https://www.ams.org/proc/2019-147-07/S0002-9939-2019-14433-6/proc14433_AM.pdf`
   (the Crossref-advertised AM link root had not yet fetched): **HTTP 403**, Cloudflare
   challenge HTML (28,968 bytes), saved `evidence/ams-AM-403-response.html`. Not a PDF.
2. **AMS canonical article page and full-HTML/MathML candidates**: `.../S0002-9939-2019-14433-6/`
   (trailing slash), `.../home.html`, `.../S0002-9939-2019-14433-6.html` — all **HTTP 403**.
3. **AMS new platform** `pubs.ams.org` (discovered from network logs): article page, DOI path
   and viewer path — all **HTTP 403**, same challenge.
4. **AMS article page in a real browser tab** (preview tool, lawful access, no interaction
   with the challenge): Cloudflare **Turnstile** "Verifying your connection"; the automated
   browser cannot pass and I did not attempt to. Stopped. This is an interactive challenge,
   not a 403 we may work around.
5. **Open-access resolvers**: Unpaywall (`is_oa: green`, only location = Manchester PURE
   landing page, `url_for_pdf: null`) and Semantic Scholar (`openAccessPdf` = the same
   Manchester landing page). Both saved in `evidence/`.
6. **Manchester Research Explorer** (frozen record re-read + author's personal site
   `sites.google.com/site/robertedwardgauntmanchester/publications`, fetched fresh, HTTP 200,
   saved): the entry for this paper links **only** to the AMS article page; the repository
   links only arXiv. No author- or institution-hosted full text exists publicly.
7. **Archives**: Wayback availability + CDX for the AM/VoR/viewer URLs on ams.org and
   pubs.ams.org — **no snapshots**; Fatcat release lookup by DOI — **empty/unavailable**;
   scholar.archive.org — fronted by an ALTCHA anti-scrape puzzle (not solvable within policy)
   and its corpus is OA captures only (AMS is paywalled here).
8. **Public mirror search** (Exa, multiple exact-phrase/DOI/article-code queries): no public
   copy of the VoR PDF or of a legitimate full HTML body anywhere. Only abstract-level
   mirrors (MaRDI, arXivlens, emergentmind, ADS).

**Secondary published-form evidence obtained (zbMATH Open, API, saved):** review 1429.33010
by Nikolaos L. Tsitsas (datestamp 2019-06-26) describes the published article as: main
results Theorems 2.1 and 2.6, an Appendix-A inequality for K with integer parameter, Appendix
B identities, tightness in limits, and an open problem posed for the I_ν integral. This is
consistent with the arXiv v2 body (which additionally contains Conjecture 2.4/Remark 2.5 on
p. 7) and confirms the published article still POSES open problems rather than settling this
conjecture — but it is a reviewer's summary, **not** a body read of the published conjecture
section. Version identification: arXiv v2 (9 Oct 2018) precedes electronic publication
(5 Mar 2019); Manchester labels the arXiv copy "publishedVersion" — metadata only.

**P1 verdict: HOLD, unchanged.** No lawful route to the actual published Conjecture 2.4 body
was available today. Remaining lawful paths require human/institutional access (library,
ILL, AMS customer service) which is outside my authorization. Nothing in this turn weakens
or clears the source gate; the arXiv-v2 statement fidelity PASS (final review) stands on its
own and is not upgraded.

## P2. Classical subsumption and substantive eligibility — adjudicated at full strength

### P2a. No published squared-order convexity / same-object three-order theorem found (bodies read)

I read actual theorem bodies (not abstracts) of every closest candidate the searches surfaced:

- **Hartman, Ann. Scuola Norm. Sup. Pisa (4) 3 (1976) 267–287**, "Completely monotone
  families…", Numdam PDF (sha256 `0274caa7…`) — **printed pages 267 and 268 rendered and
  visually read** (not OCR-only; images retained `evidence/hartman1976-p267.png/-p268.png`).
  Theorem 1.0(a): for 0<t<τ≤∞, I_μ(t)/I_μ(τ) is completely monotone in λ=μ²≥0.
  **Theorem 1.0(b), verbatim from the page image:** "Also, 1/K_μ(t) and K_μ(τ)/K_μ(t) are
  completely monotone functions of λ = μ² ≥ 0 for 0 < t < τ < ∞, so that there exists a
  distribution function W(r) = W(r, t, τ) on r ≥ 0 satisfying 1/K_μ(t) =
  [1/K_0(t)]∫₀^∞ exp(−rμ²)W(dr, t, ∞) for μ ≥ 0, K_μ(τ)/K_μ(t) = [K_0(τ)/K_0(t)]∫₀^∞
  exp(−rμ²)W(dr, t, τ) for μ ≥ 0."
  **Adjudication:** this is the closest published squared-order statement about K, but it is
  about 1/K and quotients, not K_μ(t) itself. Complete monotonicity of 1/K_μ in μ² does **not**
  imply convexity of λ ↦ K_√λ(x): a function of the form C/L(λ) with L(λ)=∫e^{−λr}dW(r) an
  arbitrary Laplace transform (Hartman's conclusion) need not be convex (reciprocals of
  Laplace transforms can be concave); Hartman's theorem is an existence statement for some
  distribution W and does not identify a measure whose transform would yield the chord. No
  one-page bridge exists from Theorem 1.0(b) to the candidate's chord/tangent comparison.
- **Hartman–Watson, Ann. Probab. 2 (1974) 593–607** — attributed content (Baricz–Ponnusamy
  proof, quote below; Hartman 1976 intro): ν² ↦ I_ν(u) and ν² ↦ I_ν(u)K_ν(v) (v≥u) completely
  monotone. First-kind statements; no K_√λ convexity. (Project Euclid full text is
  Incapsula-blocked; the K-content is pinned via the two attributions above, which agree.)
- **Baricz–Ponnusamy, "On Turán type inequalities for modified Bessel functions"**
  (arXiv:1010.3346; published Proc. Amer. Math. Soc. 141 (2013) 523–532) — full ar5iv body
  read. **Theorem 1(2), verbatim:** "the function ν ↦ K_{√ν}(u) is log-concave on (0,∞) for
  all u > 0 fixed" — derived in the proof from "(b) the function ν² ↦ 1/K_ν(u) is c.m. on
  [0,∞) for each u>0 fixed … part (b) is due to Hartman [Ha1]" plus "each nonnegative c.m.
  function is log-convex". So the literature's published fact about the *same object*
  λ ↦ K_√λ(u) is **log-concavity** (and c.m. of its reciprocal) — an opposite-shape result
  that does **not** give the linear chord/extrapolation inequality the candidate needs
  (the candidate's chord has a negative coefficient on K_{δ−1}, i.e. it is an extrapolation
  from strict convexity of λ ↦ K_√λ(x), not from log-shapes). No squared-order convexity of
  K appears in this paper.
- **Ismail, Canad. J. Math. 29 (1977)** (quotients c.m.), **Ismail–Muldoon 1978**
  (K_{ν+a}/K_ν increasing ⇒ K_ν log-convex in ν), **Cochran 1967** (I_ν order monotonicity),
  **"Complete monotonicity of modified Bessel functions", Proc. AMS 110 (1990)
  S0002-9939-1990-0993753-9** (per its indexed formula: K_{ν−1}(√x)/(√x K_ν(√x)) as a
  Stieltjes transform — argument-squared, order-fixed), **DLMF §10.37** (classical
  monotonicity only) — none states convexity/absolute monotonicity of λ ↦ K_√λ(x), and none
  states a three-order inequality of the candidate's shape
  (ν+δ)K_{δ+1} + (δ−ν)K_{δ−1} < 2δK_μ or the tangent form at δ=0.
- Mao–Tian 2023 (C. R. Math. 361) was already body-read by root (Turán defects K_ν²−βK_{ν−α}K_{ν+α});
  Yang–Tian 2022/2019 already body-read (different problems). I re-checked their abstracts in
  this turn's searches; nothing contradicts root's body-level exclusions.
- **Public proof registries searched as instructed** (see P2b) and the trureturing
  BesselProductOrderLogConvexity / BesselRatioLogConcavity pages (products/ratios, not K_√λ
  convexity).

**P2a verdict:** no explicit classical subsumer exists among accessible bodies. The published
closest-object results are about 1/K_μ, quotients, products, and log-shapes; none implies the
chord, and the ordinary-order convexity insufficiency (previous review's coefficient failures)
remains confirmed. The "two-line observation" risk (a published sentence "K_ν(x) is convex in
ν²") was not found anywhere; bounded search cannot certify absence, but no concrete material
unread body was identified as likely to contain it.

### P2b. DECISIVE: the exact conjecture is now a PUBLIC FORMALIZED PROOF (registry settlement)

The public proof registry **trureturing** (the-omega-institute.github.io/trureturing-mdbook)
contains a page **"The sharp weighted Bessel K tail bound"**
(`Problems/gaunt-2019-bessel-tail-conjecture.html`, saved `evidence/trureturing-problem-page.html`)
triaged **theorem**, citing exactly Gaunt, Proc. AMS 147 (2019) 2937–2951, DOI 10.1090/proc/14433,
arXiv:1806.00524v2, **Conjecture 2.4, manuscript page 7** — quoted verbatim on the page,
matching the frozen candidate's source statement exactly. Its evidence section states:

> **PROVED.** `D5.S3.Analytic.GauntBesselTail.Result.result` proves the complete conjunction.
> … **PROVED.** Optimality is stronger than the source's existence clause: `larger_order_failure`
> proves failure at every sufficiently large x for each r>q. The full source either/or
> statement is part of `result`. … **PROVED.** `n_one_identity` treats every real nu…

I retrieved and inspected the actual public Lean artifact
`the-omega-institute/trureturing@dev: D5/S3/Analytic/GauntBesselTail/Result.lean`
(726 lines, sha256 `9ecd83b0…`, saved). Its `claim` is literally the source conjecture:
for all real n<1, ν ≥ 1−n+√(2(1−n)), x>0, the strict bound
x^{-ν}K_{ν+n−α_{ν,n}}(x) < ∫_x^∞ t^{−ν}K_{ν+n}(t)dt; plus the source's either/or optimality
for every β ∉ {α_{ν,n}, α′_{ν,n}}; plus the n=1 equality tail ν (ν+1) x = x^{-ν}K_ν(x) for all
real ν. K is the same DLMF 10.32.9 hyperbolic integral used by the candidate. No `sorry`,
`admit`, `axiom` or `native_decide` occurs in the file (grep). The proof route is the same
mathematical route as the candidate's: strict convexity of s ↦ cosh(u√s) (squared order),
secants at (q±1)², tangent at q=0, the S_r=sinh(ru)/r tail identity, h_r with
h_r″(0)=q²−r²<0 and two-rate Laplace comparison for eventual failure, order monotonicity for
|r|<q, and the hyperbolic addition formula for n=1.

**Provenance/dates (GitHub API, saved):**
- Numerical experiment commit `772c30b3c2`, **2026-10-26T18:06:05Z**: "Add Gaunt Conjecture
  2.4 numerical check (#154)" (co-authored-by Claude Opus 5.5).
- Lean formalization commit `856e75895d…`, **2026-10-27T13:16:15Z**: "formalize: prove Gaunt
  Conjecture 2.4 (sharp Bessel K tail lower bound)".
- The live mdbook page carries the PROVED evidence and the pinned experiment link.

The candidate's frozen work is dated 28 October 2026 (root-gaunt-optimality-r3 checkpoint),
i.e. the public settlement **precedes the candidate's completed state by about a day** and is
now part of the public record. Root's earlier screen grepped *pinned* trureturing trees and
missed it; a live registry search finds it immediately.

**Adjudication.** Under the campaign counting standard ("Never count a known theorem, public
proof/refutation, …"), a public formalized proof of the exact source claim is disqualifying
for discovery credit regardless of independence or timing. This is a concrete, checkable
public artifact — not an absence-of-search-results inference. The candidate's remaining
technical surplus over the registry claim (the single closed iff statement and the explicit
eventual-strict-converse for all |r|>δ) is present in the registry artifact as lemmas
(`bessel_order_lt`, `larger_order_failure`) and is in any case an endpoint/wording variant,
not a new family.

**P2 verdict: NOVELTY-SUBSTANTIVE — FAIL for discovery credit** (public same-claim proof
exists). The separate short-classical-proof objection (P2a) is *not* what disqualifies the
candidate — I found no classical subsumer — but it is moot: the claim is public.

## Overall recommendation

1. **Keep SOURCE HOLD** (published Proc. AMS body unread; all lawful routes exhausted this
   turn and recorded with real statuses).
2. **Resolve NOVELTY-SUBSTANTIVE as FAIL for credit**: the Gaunt Conjecture 2.4 resolution
   (including optimality and the n=1 case) is a public formalized proof since 2026-10-27
   (trureturing registry). Do **not** advance this candidate to acceptance; do not count it.
   The formal/math/manuscript/packet PASSes stand as engineering facts with zero credit.
3. No manuscript edits, no new mathematical claims beyond the checked evidence above, no
   external action, no acceptance, no tally change. Root owns the final adjudication.

## Strongest finding (one line)

The exact Gaunt Conjecture 2.4 — the candidate's target claim, including optimality and n=1 —
was publicly proved and formalized (trureturing registry, Lean commit 856e75895d,
2026-10-27T13:16:15Z, same squared-order-convexity route) before the candidate's final state;
a public proof excludes discovery credit under the campaign standard. **Falsifier of this
finding:** demonstrate the registry artifact does not prove the literal claim (e.g., a hidden
premise in `besselK`, `tail`, or a frozen dependency) — the file and its pinned dependencies
are retained for exactly that check.

## Remaining holds / limits (precise)

1. Published VoR/AM body of Proc. AMS 147(7) 2937–2951 remains unread (Cloudflare Turnstile
   on all ams.org/pubs.ams.org paths; no lawful copy anywhere public). A human/institutional
   route is the only remaining lawful path. arXiv-v2 fidelity is NOT upgraded to published-body
   fidelity; the journal body could in principle differ in ways only a body read can exclude
   (residual comparison limit, unchanged).
2. Absence of a *pre-2026 published* squared-order convexity theorem is bounded (no
   MathSciNet/zbMATH full sweep, no book literature sweep); what I did check is body-level.
   This limit no longer affects credit (P2b is decisive) but is recorded for honesty.
3. The registry's Lean artifact was inspected textually (statement, route, absence of
   `sorry`/axioms) and cross-dated; I did not recompile it (not needed for the standard and
   outside this task's Lean budget). Its own bounded literature check claims no earlier
   settlement; I did not verify their build either.
4. Priority/simultaneity: the candidate lanes (28 Oct 2026) and the registry settlement
   (26–27 Oct 2026) nearly coincide; independent-priority questions are not adjudicated here
   and are irrelevant to the no-credit standard.
