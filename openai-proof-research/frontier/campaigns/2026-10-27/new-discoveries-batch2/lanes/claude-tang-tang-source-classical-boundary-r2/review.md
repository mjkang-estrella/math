# Tang–Tang o(n) stable approximation: complementary source and classical-boundary review (r2)

Review date: 2026-10-30 UTC. Solo Claude Opus 5.5 reviewer, no child agents. This is a bounded complement to `sol-tang-tang-stable-approximation-preliminary-review-r1`; it does not repeat that audit. I have no acceptance or counting authority. Counts remain **9 additional / 39 total / next 40**; root alone adjudicates.

## Disposition

| Gate | Recommendation | One-line reason |
|---|---|---|
| SOURCE (preprint) | PASS, unchanged | arXiv 1908.10024v1 pp10–11 poses the intended 2n-summand o(n) existence question. The n/2n display inconsistency remains explicit. |
| SOURCE (published) | **HOLD** | The Statistical Science 38(1) body is still unread. The only author route found (Columbia homepage) returned a Cloudflare 403 challenge. No accepted manuscript was located. |
| MATH | PASS, unchanged | I independently re-checked the steps the classical comparison depends on (below). |
| SUBSTANTIVE | **EXCLUDE (recommended)** | The analytic core, the measure and identity (1), is a published classical theorem: Lamperti 1958, and James 2010 eqs (1.1) and (2.6). The rest is the generic exponential-tilt and quantile bridge written out in full in §3. |
| PRIOR | **HOLD** | No prior proof of the o(n) statement was found in a bounded search. Liggett's 2018 unpublished manuscript and the published journal text remain unread. Nothing here clears priority. |
| Overall | **Do not INVEST; recommend EXCLUDE on substantive grounds** | The exclusion does not rest on priority or on a found duplicate. If root prefers, keep HOLD. INVEST is not supported (§4). |

The main new finding of this review answers the question the preliminary review left open: *what an existing theorem actually supplies.* The submitted "odds measure" μ_{2/3} is exactly the classical **Lamperti law**, the law of R = S/S′ for independent positive 2/3-stable variables. The submitted Bernoulli parameters p[n,j] = 1/(1+r(u_j)) are the midpoint quantiles of Lamperti's generalized arcsine law G with mean parameter 1/2 and index δ = 2/3, which is the law of S′/(S+S′). Identity (1) of PROOF.md is that law's published Cauchy–Stieltjes transform after the change of variables λ = 1/z. The preliminary review could not read a classical body (the BNF.pdf timeout). This review read two classical bodies, so the identification no longer rests only on a rederivation.

## 1. Inputs, freeze and reuse

- The scientific inputs were frozen before reading (`receipts/freeze-before.json`, 2026-10-30T12:57:36Z):
  - `frozen/PROOF.md` sha256 `b131082397e0556c82d81e121e718f908b41699849e3fa7565b3a6bea5706a4a` (from `lanes/sol-wide-analytic-mechanisms-r247/PROOF.md`).
  - `frozen/prelim-review.md` sha256 `2278b54eb40a3c8c54e40bf883e03e32ab79d4ab62e068f54f24a7eb527c820a`.
  - The after-write comparison is recorded in `receipts/freeze-after.json`.
- Administrative snapshots only: ledger.json, prior-campaign-context.json, batch and root AGENTS.md, and the two root Tang STATUS files (`admin-snapshot/`). I read the ledger's counting standard, acceptance gates and the candidate list. Comparable precedents among the candidates are mittag-modulus, fzz-q-hoggatt, coiculescu-sol-period and an-djokovic. Each was excluded or failed eligibility because an exact reduction plus a classical theorem gave the literal result, even though the ordinary proof was valid.
- Immutable references were reused, not re-downloaded. Their hashes were re-checked:
  - `../sol-tang-tang-stable-approximation-preliminary-review-r1/frozen/1908.10024v1.pdf` sha256 `707c90da…a7fe62b27`, txt `d0d307bb…c6523454`.
  - `…/frozen/1607.03036v1.pdf` sha256 `b32af89a…a479ba`, txt `50cf07a2…df3b`.
  - The 819-entry history-reference file was not re-walked.

## 2. Task 1: published or accepted text

**Result: not obtained. Published correspondence stays HOLD.**

| Route (2026-10-30 UTC) | Outcome |
|---|---|
| OpenAlex `works/doi:10.1214/22-STS852` | 200. W4312910613, online 2022-10-28. Locations: the publisher PDF (Project Euclid, *not followed*: same publisher as the challenged route) and arXiv 1908.10024 marked `submittedVersion`. No repository holds an accepted manuscript. |
| Semantic Scholar graph DOI record | 200. openAccessPdf is the same Project Euclid PDF (not followed). Only arXiv v1 is listed. |
| Wenpin Tang Columbia homepage `https://www.columbia.edu/~wt2319/` | **403, Cloudflare "Just a moment…" challenge. STOPPED** and not retried. No other Columbia host was tried. |
| Project Euclid (prior lane) | HTTP 200 Incapsula challenge. **Not retried.** |

The journal wording of Open Problem 4.6 (renumbering, the n vs 2n fix, whether it was dropped or answered in revision) is therefore **unknown**. arXiv still lists only v1 (prior lane, 2026-10-30). The preprint question stands as the operative source. Whether the journal question differs remains open.

Chronology:
- GLP arXiv 1607.03036v1: 2016-07-11. Question 3 (p12) asks for O(1) stable multiplication by 2/3.
- Liggett manuscript: 2018, unpublished.
- Tang–Tang arXiv v1: 2019-08-27.
- Statistical Science: online 2022-10-28; issue 38(1), 2023-02-01.

The Tang–Tang acknowledgment, frozen txt lines 869–871, reads: "We thank … Tom Liggett for showing us the manuscript [65]". [65] is "T. M. Liggett. Approximating multiples of strong Rayleigh random variables. 2018. Unpublished manuscript." So Open Problem 4.6 was posed *after* the authors had seen Liggett's manuscript.

## 3. Task 2: classical theorem bodies and the complete specialized bridge

### 3.1 Classical bodies read

**(L) J. Lamperti, "An occupation time theorem for a class of stochastic processes", Trans. AMS 88 (1958) 380–387.**
- DOI 10.1090/S0002-9947-1958-0094863-X; received 1956-11-30.
- Retrieved from the AMS open archive `https://www.ams.org/journals/tran/1958-088-02/S0002-9947-1958-0094863-X/S0002-9947-1958-0094863-X.pdf`. PDF sha256 `551f2c71e1f112382ca69be7ca07e1d8a483b132811a685fff03a23e1e5c4c2c`; text extraction `extracted/lamperti/lamperti1958.txt` sha256 `c1a2db11…d172`.
- Read in full, pp380–387. The relevant parts:
  - Theorem 1, eq (1.4) (p381): the limit law G_{α,δ} on [0,1] has an explicit density.
  - Proof body (3.14) and (3.17) (pp386–387): ∫₀¹ dG(t)/(t+u) = [(u+1)^{δ−1} + ((1−α)/α)u^{δ−1}] / [(u+1)^δ + ((1−α)/α)u^δ], inverted by Widder Ch. VIII to give (1.4). Footnote 2 credits Spitzer with the explicit formula.
- The OCR of (1.4) and (3.17) is noisy. My reading at α = 1/2, δ = 2/3 is confirmed by consistency checks (b) and (c) below. Those checks are diagnostics, not the authority.

**(J) L. F. James, "Lamperti-type laws", Ann. Appl. Probab. 20(4) (2010) 1303–1340.**
- arXiv 0708.0618v4 (first posted 2007-08-04; v4 2010-10-21). PDF sha256 `bc0776ff0520d1ed1f5510130d604b75cbb84999b8ab15e92dd4eab7a6c0b318`.
- Read pp1–8.
- Eq (1.1) (p2): X_α = S_α/S′_α has density (sin πα/π)·y^{α−1}/(y^{2α}+2y^α cos πα+1), attributed to Lamperti [62], Zolotarev [94] and Chaumont–Yor.
- Eq (2.6) (p7) at θ = 0: C₁(λ; X_α) = E[(1+λX_α)^{−1}] = (1+λ^α)^{−1}.
- James calls (2.5)–(2.6) "not obvious" in general. At θ = 0 it has the elementary proof in §3.2(i).

### 3.2 What the classical theorem supplies, exactly

Put a = 2/3 and θ = πa.

(i) **The measure and identity (1) are classical.**
- The PROOF.md density k(r) = (sin θ/π)·r^{a−1}/(1+2r^a cos θ+r^{2a}) is *identical* to James (1.1) at α = a (check (a): relative difference 1e−16).
- With λ = 1/z, E[z/(z+R)] = E[(1+λR)^{−1}] = (1+z^{−a})^{−1} = z^a/(1+z^a). This is PROOF.md (1), i.e. James (2.6) at θ = 0.
- Self-contained justification of (2.6) at θ = 0: let S and S′ be independent with E e^{−sS} = e^{−s^a}. Then
  E[S′/(S′+wS)] = ∫₀^∞ E[S′e^{−sS′}]·E[e^{−swS}] ds = ∫₀^∞ a s^{a−1} e^{−s^a(1+w^a)} ds = 1/(1+w^a),
  using −(d/ds)e^{−s^a} = E[S′e^{−sS′}] and Tonelli.
- For the measure-theoretic content (existence, positivity, normalization, exact density), (J)/(L) is the citable authority. PROOF.md's keyhole-contour proof is a valid alternative derivation of a known fact; it is not new content.

(ii) **The Bernoulli parameters are Lamperti generalized-arcsine quantiles.**
- T = 1/(1+R) = S′/(S+S′) has density k((1−t)/t)/t². This equals Lamperti (1.4) with α = 1/2 and δ = 2/3, namely (sin πδ/π)·t^{δ−1}(1−t)^{δ−1} / (t^{2δ}+2t^δ(1−t)^δ cos πδ+(1−t)^{2δ}) (check (b): 4e−16).
- Since u ↦ r(u) is the quantile function of R (check (d)), p(u) = 1/(1+r(u)) is the *decreasing* quantile of T.
- G_{1/2,δ} is symmetric under t ↔ 1−t, which explains p(1−u) = 1−p(u).
- So p[n,j] = midpoint quantiles of Lamperti's G_{1/2,2/3}. Lamperti's (3.17) at u > 0 is the same Stieltjes transform (check (c)).

(iii) **The spectral requirement is the *defining* transform of that law.** For a Poisson-binomial Y with parameters p_j, write r_j = (1−p_j)/p_j. Then
  n^{−1} log E e^{tY} = n^{−1} Σ_j log((r_j+e^t)/(r_j+1)).
Matching the exact normalized cumulant 3 log((1+e^{2t/3})/2) of (2/3)Bin(3n,1/2) at first order in the limit of empirical odds laws means finding a probability ν on (0,∞) with
  2∫ e^t/(e^t+r) dν(r) = 2e^{at}/(1+e^{at}) for all t,
  i.e. ∫(1+λr)^{−1} dν = (1+λ^a)^{−1}.
That is precisely the C₁-transform characterization of X_a in James (2.6). James also states that C-transforms determine the law, so **ν = μ_a is forced**. Nothing about the spectrum is chosen beyond reading off this classical law.

### 3.3 The remaining bridge, complete and independently justified

No large-deviation book body was read (no Dembo–Zeitouni retrieval). So the bridge below uses only finite elementary estimates, re-derived and checked here. Notation: Y_n = Σ_{j≤2n} Ber(p[n,j]); A_n = (2/3)X_n/n; B_n = Y_n/n; F(t) = 3 log((1+e^{2t/3})/2).

1. **Cumulant limit.**
   - g_t(u) = log(1−p(u)+p(u)e^t) extends continuously to [0,1] with p(0) = 1 and p(1) = 0. So n^{−1} log E e^{tY_n} = 2·(2n)^{−1} Σ g_t(u_j) → 2∫₀¹ g_t = 2∫ log((r+e^t)/(r+1)) dμ_a(r) by midpoint Riemann sums.
   - The t-derivative of the integrand, e^t/(e^t+r) ∈ (0,1), is bounded and continuous in (t,u). So differentiation passes under the integral and through the Riemann sums.
   - §3.2(i) gives F′(t) = 2e^{at}/(1+e^{at}). With F(0) = 0 the limit is F.
   - For A_n the normalized cumulant equals F exactly for every n.
   - F is smooth and strictly convex with F′(ℝ) = (0,2).
2. **Rate function.** I(x) = sup_t(tx−F(t)) = 3[q log 2q + (1−q) log 2(1−q)], q = x/2, on (0,2). It is strictly decreasing on (0,1], strictly increasing on [1,2), and I(1) = 0.
3. **Upper tails (Chernoff).** For Z_n ∈ {A_n, B_n} and t ≤ 0, P(Z_n ≤ x) ≤ exp(−n[tx − F_{n}(t)]). With step 1, limsup n^{−1} log P(Z_n ≤ x) ≤ −I(x) for x ∈ (0,1). Symmetrically, P(Z_n > x) has limsup rate ≤ −I(x) for x ∈ (1,2).
4. **Lower tails (finite tilt).**
   - Fix y in the open target side and t = t(y) := (3/2)log(y/(2−y)).
   - The tilt dP_t/dP = exp(tnZ_n − nF_n(t)) keeps independent Bernoulli (resp. scaled Bernoulli) summands.
   - The tilted mean → F′(t) = y by step 1. The tilted variance of Z_n is ≤ 1/(2n) (B) or ≤ 1/(3n) (A).
   - Chebyshev gives P_t(|Z_n−y| < δ) → 1, and therefore P(|Z_n−y| < δ) ≥ e^{−n[ty−F_n(t)+|t|δ]}·(1−o(1)).
   - For x < 1 take y < x and δ < x−y; for x > 1 take y > x and δ < y−x. Letting δ ↓ 0 and y → x, continuity of I gives liminf ≥ −I(x).
   - So n^{−1} log P(Z_n ≤ x) → −I(x) on (0,1), and n^{−1} log P(Z_n > x) → −I(x) on (1,2). This is a triangular array; no iid Cramér theorem is used.
5. **Uniform quantiles.** I re-checked the preliminary review's step 5 line by line; it is correct.
   - Let Q denote left quantiles and suppose, along a subsequence, Q_A(u_n) → x < y ← Q_B(u_n). Supports in [0,2] give compactness.
   - Pick c < d in (x,y) on one side of 1. This is possible even when the gap straddles 1.
   - If d < 1: P(A_n ≤ c) = e^{−nI(c)+o(n)} < e^{−nI(d)+o(n)} = P(B_n ≤ d), because I(c) > I(d).
   - If c > 1: P(A_n > c) > P(B_n > d), because I(c) < I(d). This gives the same CDF ordering.
   - Eventually Q_A(u_n) < c and Q_B(u_n) > d, so u_n ≤ P(A_n ≤ c) < P(B_n ≤ d) < u_n, a contradiction. Exchange A and B for the opposite gap.
   - No restriction on u_n is needed, so atoms and superexponentially small levels are covered. Hence sup_u |Q_A − Q_B| → 0.
   - The comonotone coupling (Q_A(U), Q_B(U)) gives W∞(A_n, B_n) → 0. Multiplying by n, W∞((2/3)X_n, Y_n) = o(n).

Steps 1–5 use nothing about a = 2/3 beyond the classical transform in §3.2. The same template appears to apply unchanged to a·Bin(m,1/2) for rational a ∈ (0,1) with am an integer, using am summands drawn from the Lamperti law of index a, because the supports then share endpoints. This is offered only as an indication that the template is generic. I did not check it separately, and it is not claimed as a result.

### 3.4 Residual invention, stated exactly

What is *not* supplied by a read classical body:

(R1) The observation that, for this problem, W∞ = o(n) is decided at speed-n large-deviation order. So it suffices to match the limiting normalized cumulant, which in turn means matching the C₁-transform of the empirical odds law.

(R2) Recognizing the required transform (1+λ^{2/3})^{−1} as Lamperti's, and discretizing by midpoint quantiles.

(R3) Steps 1–5 above.

- (R2) is a lookup of the defining transform of a named law.
- (R3) is the standard exponential-tilting proof of a speed-n LDP for a triangular Bernoulli array, plus a short compactness lemma comparing quantiles of two sequences with a common strictly monotone rate.
- (R1) is the only conceptual step. It is the standard Gärtner–Ellis heuristic: a common limiting log-MGF gives a common rate function.
- The step Tang–Tang actually lacked was choosing nonuniform parameters. Their equidistributed choice p_i = i/(2n+1) has odds law with C₁-transform ≠ (1+λ^{2/3})^{−1}, which is why it gives Θ(n). The fix is to take parameters from the law (R1) forces.

Under the ledger standard ("Never count … routine corollary … parameter instance"; precedents mittag-modulus, fzz-q-hoggatt, coiculescu), this is a **routine classical corollary**: classical identity, then generic LDP, then quantile comparison. The result is also strictly weaker than the posed conjecture: Acc(2X/3) = O(1) ([47] per Tang–Tang p10; GLP Question 3, p12) remains open and is not addressed.

## 4. Why INVEST is not supported

An INVEST case would need either (a) a step whose difficulty survives the identification above, or (b) evidence that the o(n) question was a recognized hard obstacle that the classical route could not trivially overcome. Neither holds.
- (a) Every step is either a published identity (L/J) or the generic bridge in §3.3. The preliminary review already found the hardest-looking step, extreme quantiles, to be a five-line compactness argument; I concur.
- (b) Tang–Tang give one failed trial (equidistributed parameters) and pose the question. That shows the question was asked, not that it was hard. Typographic openness and failed searches are not novelty evidence (batch AGENTS.md).
- The spectral identification is real and pleasant: the Lamperti law/generalized arcsine appears as the "right" parameter distribution. But under the campaign's rule it is a parameter-level application of a known transform, not a new mechanism. Root may weigh this differently. If so, the strongest honest framing is "a short classical solution of an explicitly posed sub-question". It would still need SOURCE (published) and PRIOR (Liggett) resolution before any further gate.

## 5. Task 3: Liggett 2018 and closest author/citer bodies

- **Liggett 2018 manuscript: not obtained.**
  - OpenAlex exact-title search returned 1 hit, which is Tang–Tang itself (citing).
  - arXiv `au:Liggett` (21 results, newest first) has no 2017–2020 entry with this or a similar title. The newest Liggett entry is 1804.06877 (2018-04-18, Liggett–W. Tang, one-dependent colorings, unrelated).
  - The prior lane's exact-title arXiv query had 0 hits.
  - `https://www.math.ucla.edu/~tml/` returned 404.
  - No other route was tried. **No absence claim is made.** The title ("Approximating multiples of strong Rayleigh random variables") is squarely on topic, so this is the **largest residual PRIOR risk**. Mitigating fact only: Tang–Tang posed Problem 4.6 after seeing it.
- **What Tang–Tang reproduce from it** (Theorem 4.7 and pp12–13, frozen txt lines 674–699):
  - Hurwitz stability of the PGF of ⌊2X/3⌋, and hence factorization into positive-coefficient factors of degree ≤ 2.
  - So ⌊2X/3⌋ is a sum of independent {0,1,2}-valued variables, W∞-within 2/3 of 2X/3.
  - It is **not** a Poisson binomial: a positive quadratic factor with nonreal roots is not a product of Bernoulli PGFs. Splitting each quadratic into Bernoullis is not available in general. So Theorem 4.7 does not imply, and is not an erroneous source of, the o(n) Bernoulli statement.
  - Tang–Tang's ⌊jX/k⌋ examples (f ∈ Q₃∖P₃, etc.) concern Conjecture 4.8, not Problem 4.6.
- **GLP 1607.03036v1:** the prior lane's reading stands: stable floor-division by interlacing, failure explained for 2/3 (txt line 659), and Question 3 (line 661) asking for O(1). It does not prove the o(n) statement.
- **Bounded citer screen (titles only; 2026-10-30):**
  - OpenAlex cites:Tang–Tang: 32 records. All titles are listed in `downloads/openalex-citers-tang/body`. None is about multiplying a Poisson binomial by a constant. The closest-sounding, Fontana–Semeraro "The Bernoulli structure of discrete distributions" (arXiv 2410.13920, ECP 2025), concerns dependent Bernoulli polytopes per its abstract; it is irrelevant.
  - OpenAlex cites:GLP: 11 records.
  - The closest body, Michelen–Sahasrabudhe arXiv 1804.07696v2, was fetched (sha256 `5a8de2dc…3b0e`) and scanned. Its only GLP connection is a CLT variance-condition improvement (txt lines 142, 161, 768); it contains no multiplication or 2/3 content.
  - Other GLP citers by title (hyperuniform survey, paving, tail triviality, Lieb–Sokal, anti-concentration, Marcinkiewicz CLT, down-up walk) are off-topic. Their bodies were not read.
  - Two arXiv abstract keyword queries (strong Rayleigh × multiple/multiplication/2/3; Poisson binomial × Wasserstein/strongly Rayleigh) returned nothing on point. The first query's results were evidently mis-parsed by arXiv and are preserved as returned.
  - This is a bounded, title-level screen. It is not exhaustive and does not clear priority.

## 6. Concrete gaps remaining

1. The published Statistical Science problem text is unread. Every lawful route found is challenged; root must not bypass.
2. Liggett 2018 is unread and on topic. Prior-art status is unknown.
3. Current public proof-registry heads were not checked in this lane. They remain explicit holds, as instructed: no HEAD loops and no GitHub routes.
4. Lamperti (1.4)/(3.17) were read from OCR. The specialization is confirmed by consistency diagnostics and by James (1.1)/(2.6), not by a clean typeset re-reading.
5. The O(1) conjecture and the second Open Problem 4.6 question (lower bound of Acc) are untouched.

## 7. Checks, provenance and access discipline

- `scripts/checks.py` → `check-results.json`, guarded. It ran with exit 0, peak group RSS 11.4 MB, wall 0.60 s. Results:
  - (a) density equals James (1.1): rel 1.1e−16.
  - (b) pushforward to T equals Lamperti (1.4) at α = 1/2, δ = 2/3: rel 3.6e−16.
  - (c) total mass 1 to 2e−12. At five z values, quadrature of ∫z/(z+r)dμ, z^a/(1+z^a) and James (2.6) agree to about 1e−12, and Lamperti (3.17) matches quadrature to about 1e−11.
  - (d) CDF(r(u)) = u to 1e−16.
  - These are diagnostics only; the proofs are §3.2–3.3.
- All retrievals used `scripts/fetch.py` under the fixed helper_guard (no cap raises), with single attempts and no retries. Receipts with UTC, status, final URL, bytes, sha256 and access class are in `receipts/access.jsonl` (21 entries). The 403 was classified STOP-denied and its host was not retried. One OpenAlex filter request returned 400 (malformed query) and was replaced by a search query.
- No publisher, ScienceDirect, Google, GitHub API/raw/codeload/diff/patch, browser, proxy or TLS-disable route was used. No external messages. No MathDB, Lean, manuscript, shared, ledger, count or git edits.
- Procedural deviations are in FAILURES.md.
- `manifest.json` lists every lane file except itself and `verification-receipt.json`. A separate guarded `scripts/verify.py` run checks it and the freeze.
