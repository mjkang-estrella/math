# Preliminary independent review — gamma-level convexity candidate (root-gamma-level-r1 @ 4bffd200db)

Reviewer: pi-gamma-level-preliminary-review-r1 (Pi GLM-5.3-Flash-EXL3, thinking high, standard speed). SOLO, no children. No git operations; no shared/parent edits; frozen parent lane bytes verified unchanged before and after this review.

Candidate under review: for every c>1 and x>0 a unique h_c(x)>0 with Gamma(h_c)Gamma(h_c+2x)/Gamma(h_c+x)^2 = c, and h_c strictly convex on (0,∞); c=2 resolves Remark 16(a) of Garrappa–Gerhold–Popolizio–Simon. One family; the all-c statement is not separately countable.

## Per-gate verdicts

| Gate | Verdict | Summary |
|---|---|---|
| SOURCE | **PASS** | Both PDF pages of arXiv v4 Lemma 15/Remark 16(a) visually read by me from the frozen bytes; published JMAA version-of-record also now fetched and visually read — identical. Theorem 23 confirmed to use h at α≤1. |
| MATH | **PASS** (ordinary proof; no Lean claimed or checked) | Every step independently re-derived; no gap found. Own different-algorithm numerical checks all pass. |
| NOVELTY | **PASS at bounded-screen level** (residual abstract-lemma risk recorded) | No prior resolution of Remark 16(a) and no subsuming theorem found in the bounded screen. Himmel–Matkowski inspected in full: does not match. |
| SUBSTANTIVE | **PASS — recommend eligibility**, root adjudication required | Explicit open belief of a JMAA paper whose own method provably fails on the missing interval; the (0,1) range is used by the source's own Theorem 23. Same eligibility shape as accepted first-batch #23 (Simon threshold). Not a credited-family variant. |

No acceptance or count is made or implied. Lean endpoint, paper, extracted replay remain open gates. An honest HOLD would have been acceptable; the math and source gates came through clean, so the recommendation is to proceed to the expensive gates **after root confirms substantive adjudication**.

## SOURCE gate (PASS)

1. I rendered pages 9–10 of the frozen `sources/arxiv-v4.pdf` (SHA256 b40a207a…) myself with pdftoppm and read them visually. Page 9: Lemma 15 exactly as cited — unique y=h(x)>0 with 2Γ(x+y)²=Γ(y)Γ(2x+y) (≡ Γ(y)Γ(y+2x)/Γ(y+x)²=2), real-analytic, increasing, h(1)=1, h′(1)=2, h(x)∼x²/log2, strict convexity proved **only on [1,∞)** (via h″>0 on [h⁻¹(1/2),∞)). Page 10: Remark 16(a) verbatim: "We believe that h is strictly convex on the whole (0,∞)… it can be shown from the convexity of the function 1/ψ′ on (0,∞) … that the function H(x,y,z) takes positive values on (0,∞)³. It seems that a more technical analysis is necessary in order to prove the convexity of h on (0, h⁻¹(1/2)]."
2. **Journal body closed (new)**: the root's official-repository 403s were bypassed legitimately — the TU Wien reposiTUm open-access copy is the Elsevier **version of record** (J. Math. Anal. Appl. 551 (2025) 129588, Producer: Elsevier, 24 pp., CC BY-NC-ND). I visually read its p.13: Lemma 15, Remark 16(a),(b), Proposition 17, Corollary 18 are word-identical to arXiv v4. Saved and hashed in my lane (`sources/jmaa-vor.pdf`, SHA256 ad4b04d7…). The candidate's caveat "indexed text is not a visual journal-body comparison" is thereby discharged at this review level.
3. arXiv submission history: v4 (11 May 2025) is the **latest version**; journal reference JMAA 551(1) 2025 129588, DOI 10.1016/j.jmaa.2025.129588 confirmed on the abs page.
4. Theorem 23 (journal p.19–20, and v4 text): log-convexity ⇔ α≤1 and β ≥ h(α); log-concavity ⇔ α≥1 and β ≤ h(α). The proof *uses h(α) at α<1* (only-if parts and the u₁≥u₀ seed). So the "obsolete v2 only-needed-≥2 framing" correction is right: in v4/journal the small-α values of h are load-bearing in a main theorem.
5. Conjecture 26 (journal p.23) is separate and is **not** claimed resolved: its hypothesis is "log E_{α,β} is a complete Bernstein function", with log E explicitly "up to translation" — the candidate correctly takes no credit there. Remark 16(b)'s asymptotic expansion is untouched.

## MATH gate (PASS, ordinary proof)

I re-derived every step of PROOF.md independently. Checklist with results:

- Euler product bridge: F(x,s)=logΓ(s−x)+logΓ(s+x)−2logΓ(s)=Σ_{m≥0}−log(1−x²/(s+m)²). The root verified only a one-factor algebraic identity; **I verified the full bridge numerically within a rigorous tail bound** (trigamma ψ₁(s+M+1) tail, −log(1−t)≤t/(1−t)) at 6 points incl. x/s near 1 and near 0 — see `ownchecks.py`, `ownchecks-result.json`. The identity is classical (Euler/Weierstrass product), but this closes the loop.
- g(u)=−log(1−u⁻²): g′=−2/(u(u²−1)), g″=2(3u²−1)/(u²(u²−1)²)>0 on (1,∞) — re-derived symbolically (own script, independent simplification). g strictly convex and decreasing. Note the proof needs no differentiability of F at all — only termwise monotonicity and Jensen.
- Local uniform convergence on compacts of {0<x<s}: terms ≤ C/(s_min+m)². Verified argument. (My first own tail bound was wrong — used 1/(s+M+1) instead of ψ₁ — and failed; fixed in my script. The candidate's written proof is unaffected; it does not do numerical tails.)
- Existence/uniqueness of ρ(s)∈(0,s): F strictly increasing in x (every term strictly increasing), F→+∞ as x→s⁻ (m=0 term), F(0,s)=0, log c>0 for c>1. Correct. For c≤1 no solution exists (Γ log-convexity gives ratio ≥1), so c>1 is the full parameter range — the family statement is complete as given.
- ρ strictly increasing (F strictly decreasing in s, termwise, strict via any fixed term), ρ(s)→0 as s→0⁺ (ρ<s), ρ→∞ as s→∞ (F(M,s)→0 by dominated convergence; correct). Continuous strictly increasing bijection (0,∞)→(0,∞); inverse s_c continuous strictly increasing.
- Strict concavity of ρ: the weight identity (S+m)/X = a(s₀+m)/x₀+(1−a)(s₁+m)/x₁ with a=λx₀/X∈(0,1) — verified by direct expansion. All ratios >1 since xᵢ<sᵢ. Jensen termwise with at least one strict term among m=0,1: equality in both would give s₀/x₀=s₁/x₁ and (s₀+1)/x₀=(s₁+1)/x₁ ⟹ 1/x₀=1/x₁ ⟹ x₀=x₁ ⟹ s₀=s₁, contradiction (ρ injective). All termwise gaps ≥0, series absolutely convergent, so the positive gap survives summation: F(X,S)<log c, hence X<ρ(S). Correct.
- Inverse of increasing strictly concave is strictly convex (applied to s_c), then h_c=s_c−id is strictly convex on (0,∞). Correct. h_c(x)>0 for all x>0 since s_c(x)>x (ρ(s)<s). Correct.
- No circularity: the proof never differentiates the implicit curve, so the source's known obstruction (H(x,y,z)>0 on (0,∞)³, i.e. the h″-sign route fails) does not apply to it. This is exactly why the route is *genuinely different*, not a patch.
- Cross-check of my own: Newton solve of the ratio directly in h (different variable, different algorithm than root's bisection on ρ): h(1)=1 and h′(1)=2 at c=2 (source anchors), h(x)/x²→1/log 2, 32 positive second central differences of h_c for c∈{1.01,1.2,2,5,100} on grids including x∈{0.002,…,100}, 12 strict midpoint-convexity gaps, and F(h,h+1)=log 2 consistency. All pass. Diagnostics only, not certificates.

Weak points scrutinized and found sound: summation of termwise Jensen inequalities (absolute convergence + nonneg gaps + one positive gap); domain of g (all arguments >1, using X<S which follows from xᵢ<sᵢ); a∈(0,1); injectivity of ρ needed for x₀≠x₁ — present. The "at least one of m=0,1" argument is tight (m=0 alone can be equality for non-identical pairs; m=1 rescues it — this is why two terms are needed and why the shift structure matters).

No Lean or paper exists; none is claimed. The PROOF.md correctly labels its checks as diagnostics. Minor nit: PROOF.md cites "`Real.BohrMollerup.tendsto_log_gamma`"; the pinned Mathlib (d13f23b723) actually has `Real.logGammaSeq` (BohrMollerup.lean:140) and `Real.BohrMollerup.tendsto_logGammaSeq` — name slip, feasibility observation unchanged and confirmed by me.

## NOVELTY gate (PASS at bounded-screen level; limits recorded)

Independently inspected:

1. **Himmel–Matkowski, JCA 25 (2018) 927–938** (fetched the official PDF myself, read all 12 pages): Thm 3.1 and 3.5 characterize B(x,x+k) via the functional equation φ(x+1)=x(x+k)(2x+k+1)/(2x+k)·φ(x) plus log-convex/geometric-convex sections (Krull / Gronau–Matkowski); Section 4 is beta-type functions; Section 5 is directional-convexity Hessian remarks (Ex. 5.2, Cor. 5.3). **No implicit gamma-ratio level-curve theorem, no Orlicz-mean content.** Root's characterization of this paper is accurate.
2. **MSE 1337411**: "Proving injectivity of a multivariable function" — injectivity of x↦(Γ(4x+y)Γ(y)/Γ(2x+y)², Γ(4x+y)Γ(2x+y)/Γ(3x+y)²). Different question (injectivity, not convexity of a level curve); no visible answers. Not inferred as solved or as blocking.
3. **MathDB 349140 (accepted first-batch #23, Simon threshold)**: read the first-batch record in prior-campaign-context.json — a different source question (Le Roy parameter threshold convexity, Simon arXiv:2012.11018), different function, with perspective/supremum tools explicitly uncredited there. The present candidate is **not** a variant of that credited family: different curve, different source, and the shared classical tool (perspective-type weighted Jensen) receives no credit in either. This is the correct distinction; the shared-tool overlap is real and disclosed.
4. **Citation/follow-up screen**: the JMAA record shows ~2 citations; the closest citing work, Ferreira–Simon "Mittag-Leffler functions and convex ordering" (arXiv:2512.04940), was fetched and checked — it does not mention h, Remark 16, or Conjecture 26 (subject: monotonicity of E_α in α via convex ordering). Simon's publication list and Gerhold's arXiv list show no follow-up resolving Remark 16(a). No public resolution found.
5. **Abstract-mechanism screen** (the routine-subsumption risk): searched for any published lemma of the form "for strictly convex decreasing g with convergent shifted perspectives Σ g((s+m)/x), the level radius is (strictly) concave" or convexity of its sublevel sets. Nearest genres inspected: convexity of level sets of inverse σ_k equations (Lin, arXiv:2209.11370 — different setting), Simon–Verovic strictly convex epigraphs (arXiv:1604.00270 — abstract characterization, no such instance), perspective-function literature (arXiv:1610.01552 — perspective is jointly convex, but Σ g((s+m)/x) is *not* a perspective sum and joint convexity actually fails for individual terms g(t/x); the candidate's weighted argument is a distinct quasiconvexity mechanism). **No subsuming lemma found.** Note: a single term g((s+m)/x) has convex sublevel sets trivially (linear-fractional inequality); the content of the proof is that the *sum over the shift lattice* stays quasiconvex with a strictly concave boundary — this is not a classical triviality.
6. Recorded limits of the screen: ScienceDirect/Scopus citing lists not directly crawled; Web of Science unavailable; the Orlicz-means and harmonic-mean convexity literature (e.g., Matkowski-type mean results) only partially screened via keyword search; MathDB records not exhaustively re-pulled for new entries. No novelty claim beyond this bounded screen; empty search results are not proof of absence.

## SUBSTANTIVE gate (PASS — recommendation, root adjudicates)

Arguments for eligibility:
- Remark 16(a) is an explicit open belief stated in a peer-reviewed JMAA paper, and the authors *prove their own method fails* on the missing interval (H>0 on (0,∞)³, from convexity of 1/ψ′). Resolving it therefore requires a different mechanism — which the candidate supplies. This is the same eligibility shape as accepted first-batch #23: an exact source question closed with a classical-but-uncredited tool.
- The interval (0,1) is not a dead endpoint: the source's own main Theorem 23 evaluates h(α) for α<1, and the paper's Figs. 1–2 draw h on all of (0,∞) as a separator curve. The shape of the boundary on (0,1) is part of the source's own main results' boundary behavior. I therefore **reject** the reading that this is a mere parameter-range extension: the source did not prove a theorem missing an endpoint correction; it stated an open conjecture covering an interval where its method provably fails.
- The all-c>1 theorem is ONE family (c=2 is the source instance); no separate counting of levels. The candidate itself proves all c simultaneously — there is no cheaper "subsumption bridge" that would make the general statement routine; the general-c statement shares the same single proof.
- Shortness is not ineligibility: the proof is ~1 page but the question is exact, published, unresolved, and resistant (source's route provably fails).

Strongest objection (stated explicitly, per task):
> The weighted-Jensen mechanism is generic: if any published abstract lemma covers "level radius of Σ g((s+m)/x) is strictly concave for strictly convex g", the candidate collapses to a routine instantiation, and the residual mathematical content is convexity on (0,1) for one special function — which a strict evaluator could still class as a bounded parameter-range completion. My bounded screen found no such lemma, and the source's own failed-method statement shows the instance is not a corollary of standard digamma-convexity tools; but this objection is the one remaining HOLD-level risk and should be weighed by root.

Secondary objection (answered): "does not resolve anything the source uses" — answered: Theorem 23's boundary classification and Fig. 1/2 separator curves rest on h's actual shape; strict convexity on (0,1) pins that shape (e.g. it rules out changes of curvature of the log-convexity/log-concavity boundary below α=1). It also upgrades Proposition 17/Corollary 18's boundary (β>h(α) ⟹ non-real zeros) with a globally convex boundary curve. Not a proof-use gap, but real structural content.

## Gaps (unchanged open gates)

1. No Lean endpoint; none attempted (correctly deferred until eligibility cleared).
2. No paper, no extracted deterministic packet/replay.
3. All numerical work (root's and mine) is diagnostics, not interval certificates.
4. Bounded novelty screen only; the abstract-lemma risk above.
5. My review is preliminary; per task, root alone accepts.

## Provenance and integrity

- Frozen parent lane byte-identical before and after review (all six provenance.json hashes re-verified; `git diff 4bffd200db -- <lane>` empty).
- Own artifacts written only in `lanes/pi-gamma-level-preliminary-review-r1/`: `ownchecks.py`, `ownchecks-result.json`, `sources/jmaa-vor.pdf`, `review.md`, `provenance.json`.
- No external messages/posts/uploads; only public reads (arXiv abs page, JCA PDF, TU Wien reposiTUm open-access PDF, MSE via search snippets, arXiv HTML of 2512.04940). MSE direct fetch returned 403; not retried via bypasses.
- v4 confirmed latest version; journal vor confirmed identical on the read pages.
