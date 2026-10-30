# Preliminary adversarial review — arcsinh_p concavity refutation (MathDB 325512)

Reviewer: independent preliminary reviewer (own lane `pi-arcsinh-concavity-preliminary-review`, solo, no children).
Candidate: parent lane `parent-arcsinh-concavity`, frozen and hash-verified (13/13 files match `preliminary-review-hashes.json`).

## VERDICTS

| Gate | Verdict |
|---|---|
| SOURCE | **PASS** — literal statements verified in arXiv v2 (latest), the publisher-typeset Filomat 29:2 (2015) 303–313 body, and live MathDB 325512 |
| MATH | **PASS** — witness and proof independently rederived from scratch; all exact values confirmed |
| BOUNDED NOVELTY | **No prior resolution found** (search negative, but bounded; see limits) |
| SUBSTANTIVE ELIGIBILITY | **FAIL — uncountable parameter-domain correction. Credit 0. No Lean investment recommended.** |

## 1. SOURCE gate — PASS

Verified literal statements, all agreeing:

- **arXiv:1305.0938v2** (v2, 25 Oct 2013 — confirmed latest version via fresh abs-page fetch; journal ref Filomat 29(2) 2015 303–313): *Conjecture 1. For x ∈ (0,1) fixed, the function p ↦ arcsinh_p(x) is strictly concave on (0,∞).* With arcsinh_p(x) = ∫₀ˣ (1+t^p)^(−1/p) dt (paper eq. for arcsinh_p, p. 2). Preceded by "Based on computer experiments we believe that the following results are true."
- **Published Filomat 29:2 (2015) 303–313, DOI 10.2298/FIL1502303B** — *Conjecture 2.4*, verbatim identical to arXiv Conjecture 1 (strict concavity on (0,∞); "In particular" Turán clause restricted to p > 1 only because arcsinh_{p−1} needs p > 1). Verified by direct visual/text inspection of the publisher-typeset PDF ("Filomat 29:2 (2015), 303–313 / DOI 10.2298/FIL1502303B" running heads; marked "Version: Published version"), sha256 `e59765ca7b80b12f3f8ec3e3ed700220c1eca70561fdbbb02c527361a22b2208` (saved in this lane as `filomat-published-jyx.pdf`/`.txt`).
- **MathDB 325512** (fresh fetch of `https://mathdb.com/api/posts/325512`, responseId `mvqnnprdt8z122`): open conjecture, statement quantifies **strict concavity on (0,∞)**; `comments`, `solutions`, `model_attempts`, `human_solves` all empty; byte-identical to the frozen `325512-live.json` copy.

**Access limits:** `doiserbia.nb.rs` timed out for me on three direct attempts (PDF via fetch tool ×2, `ft.aspx`/`Article.aspx` via curl exit 124). I substituted the publisher-typeset "Published version" deposit (JYX institutional repository, rights-retention copy) plus the doiserbia-hosted snippet returned by search, which show the identical Conjecture 2.4 text. The final typeset statement does not differ from arXiv v2.

## 2. MATH gate — PASS (independently rederived)

My own checker `checker_review.py` (this lane) rederives everything from scratch — binomial-truncation coefficients built from `math.comb`, polynomial identities by exact integer convolution, sign directions from all-positive remainders, exact rational integration via `fractions.Fraction`:

- Substitution t = u^N: F(1/N, 2⁻¹²) = N∫₀^(2^(−12/N)) u^(N−1)/(1+u)^N du; limits 1/8 (N=4) and 1/4 (N=6) for x = 1/4096. ✓
- (1+u)⁴P₃ = 1 − u⁴(35+84u+70u²+20u³) ⟹ P₃ ≤ (1+u)⁻⁴; (1+u)⁶P₆ = 1 + u⁷(792+3465u+6160u²+5544u³+2520u⁴+462u⁵) ⟹ P₆ ≥ (1+u)⁻⁶, both for u ≥ 0. ✓
- L = 4∫₀^{1/8} u³P₃ du = **2291/13762560**; U = 6∫₀^{1/4} u⁵P₆ du = **1574453/19377684480**; midpoint defect ≥ (L−2U)/2 = **38411/19377684480 > 0**. All match the candidate exactly. ✓
- Independent 50-dps cross-check by two methods that do not use the polynomial route (adaptive quadrature and the absolutely convergent hypergeometric series F(p,x) = Σ(−1)ʲ(1/p)_j/j! · x^{jp+1}/(jp+1), agreeing with each other): F(1/12)=2.7210e−6, F(1/6)=7.73079e−5, F(1/4)=1.67351e−4; defect = 7.727961189e−6 > 1.982e−6 bound. The witness is valid: **F(p,x) is not concave in p at x = 1/4096**; the literal published conjecture is false.

No Lean exists; per instructions formal completion was **not** assessed or demanded.

## 3. BOUNDED NOVELTY gate — no prior resolution found (bounded)

Read the actual theorem bodies of all three named prior-art items (parent's author-hosted copies, hash-verified):

- **Karp–Prilepkina, JMAA 421 (2015) 370–382 / 1402.3357.** Theorems 1–2 concern the *forward* functions: p ↦ sin_p(y) strictly log-concave (y∈(0,1)); cos_p, tan_p on (1,∞); p ↦ sinh_p(y) strictly **log-convex**, cosh_p log-convex, tanh_p strictly concave (y ∈ (0,∞)). Literal direction checked as instructed: log-convexity of the forward sinh_p says nothing about concavity of the inverse-integral arcsinh_p; no statement about p ↦ arcsinh_p(x) appears.
- **Karp–Prilepkina, Mathematics 2024, 12, 3383 / 2411.13442.** Two-parameter results: Corollary 1 p ↦ sin_{p,q}(y) concave on (1,∞); Theorem 4 p ↦ sinh_{p,q}(y) log-convex on (1,∞); monotonicity tables. Nothing on concavity of p ↦ arcsinh_{p,q}(x) in p. The paper itself states results "are not complete."
- **2019 survey (jmi-13-58, Bhayo–Pogány–Vuorinen).** Its *Conjecture 5.1* restates the problem as **strict concavity of p ↦ arcsinh_p(x) on (1,∞)** — the domain is silently narrowed from the source's (0,∞), and the derived Turán clause is correspondingly adjusted from p>1 to p>2. The survey contains **no counterexample and no claim that concavity fails on (0,1)**. Note the survey systematically paraphrases *all* domains of [6]'s already-proven theorems as (1,∞) (its "Theorem 5.1 ([6] Theorem 1)" vs the actual (0,∞) statements), so the narrowing reads as a p-Laplacian convention; but its internally consistent Turán adjustment shows it was deliberate. Either way, no small-p obstruction is stated, proved, or implied anywhere in it.
- **MathDB 325512**: no comments/solutions/model attempts (fresh fetch). **trureturing** local checkout: no "arcsinh" occurrences. **count-ex-machina**: not present in the local checkout — unverified, recorded as a limit. Web searches (incl. the 2026 Darkunde–Ghodechor DRNA paper, read: no arcsinh/concavity content) found **no posted, proved, or implied counterexample** and no resolution of Conjecture 2.4 / Conjecture 5.1 in either direction.
- The candidate's proposed small-p obstruction is therefore **not** already posted, and **not** implied by any existing parameter-limit theorem. The "p→0 flatness" heuristic does not by itself contradict concavity (F(p,x) → 0 as p→0⁺ is compatible with concavity; a concave function may vanish at an endpoint), and my own attempt to make the asymptotic argument uniform hit genuine numerical cancellation — the failure genuinely requires an explicit witness. It is a new observation, not a known corollary.

**Limits:** the full citing corpus of 1305.0938 (9 citing works listed by Filomat) was not exhaustively read; count-ex-machina unverified; the small-p region p ≲ 0.15 resisted reliable numerics by both my methods (boundary-layer quadrature error and series cancellation at x^p → 1), so claims there are only from the exact proof. No worldwide-priority claim is made or inferable.

## 4. SUBSTANTIVE ELIGIBILITY — **FAIL: parameter-domain correction (credit 0, no Lean investment)**

This is the decisive gate, judged explicitly against the user's strict standard, not waved away in either direction.

**The facts:**

1. The proven witness uses only p ∈ {1/12, 1/6, 1/4} ⊂ (0,1).
2. The most recent community restatement of the open problem — the 2019 survey's Conjecture 5.1, by authors including two of the three source authors, with the derived clause deliberately adjusted (p>1 → p>2) — lives on **(1,∞)**. The motivating p-Laplacian eigenvalue problem has 1 < p < ∞.
3. My own numerics (two independent methods, 50 dps) show that at the witness x = 1/4096 the second symmetric difference is **negative (concave) at every sampled p > 1**: D(1)=−3.17e−8, D(1.5)=−5.87e−10, D(2)=−1.078e−11, D(3)=−3.74e−15, D(5), D(10) — and for large p this is provable in outline: F(p,x) = x − x^{p+1}/(p(p+1)) + O(x^{2p+1}) with the deficit d(p) = x^{p+1}/(p(p+1)) strictly convex (d″/d = (ln x)² + 1/p² + 1/(p+1)² > 0), so F is strictly concave for large p at small x; error terms at p=2, x=2⁻¹² are O(2⁻⁶⁰), eight orders below D(2). The same holds at x = 0.9 (concave at p = 0.5…4). **The surviving (1,∞) conjecture is numerically consistent at every point I sampled and remains open.**
4. Hence the true mathematical picture is: concavity *fails* on a small-p region (containing the witness) and appears to *hold* on (1,∞). The candidate's established result therefore says exactly: "the source's claimed parameter domain (0,∞) is wrong on (0,1); the correct domain is (1,∞) (where the question remains open)." That is the precise shape of an **uncountable parameter-domain correction**: the surviving statement is untouched, and what is established is a correction to the quantified domain of a claim whose intended/live form excluded the witness region anyway.

**Why this fails the strict standard:** the campaign counts genuinely new substantive resolutions, not domain/scope corrections. The closest accepted precedent (classical-means, #8) refuted the source's proposed range *and* completed the full classification of both directions; the witness refutations accepted (#3, #16) left no surviving narrower live form of the conjecture. Here a live, deliberately restated narrower conjecture survives untouched, and the candidate proves nothing about it. That the literal published and MathDB-curated quantifier is (0,∞) — and that the refutation is genuinely new (novelty sweep negative) and non-trivial to find (the source's own computer experiments missed it) — is recorded and real, but under the user's strict standard it does not convert a domain correction into a substantive discovery. Per instruction: **verdict FAIL, eligibility credit 0, no Lean investment recommended for the candidate as proposed.**

**What would make it substantive (for the parent's information, not counted here):** resolving the *surviving* conjecture — i.e., proving or refuting strict concavity of p ↦ arcsinh_p(x) on (1,∞) (survey Conjecture 5.1) — or producing a rigorous p>1 failure if one exists. My numerics found no p>1 failure and suggest the (1,∞) conjecture is true; proving it would be a genuinely new theorem but is a different, harder project than the present candidate.

## Decision

- SOURCE PASS, MATH PASS, novelty search negative (bounded).
- **SUBSTANTIVE ELIGIBILITY: FAIL — parameter-domain correction. Candidate credit 0. Campaign accepted count stays 23/30. No Lean investment recommended. No formal or manuscript PASS is claimed.**
- Decisive objection (single): the witness lies entirely in the parameter region (0,1) that the live restated conjecture (survey Conjecture 5.1, (1,∞)) already excludes, and the surviving conjecture appears true (numerically) and is untouched by the candidate; the established result is therefore a domain correction under the strict standard, notwithstanding the literal (0,∞) quantifier of the published source.
