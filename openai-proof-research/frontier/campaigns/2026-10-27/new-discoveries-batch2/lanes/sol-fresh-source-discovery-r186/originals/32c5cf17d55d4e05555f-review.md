# SOLO independent adversarial FINAL review — gamma-level convexity (root-gamma-level-complete-r3 @ c0bbeeddfc)

Reviewer: pi-gamma-level-final-review-r1 (Pi GLM-5.3-Flash-EXL3, thinking high, standard/default speed). SOLO, no children. I am independent, not an author of the reviewed bytes. No git operations; no candidate/shared/ledger edits; no external posts. Frozen lane verified 44/44 before and after this review (content hashes, below). My own byte-copy of the packet was made and reviewed; nothing was taken on trust from the parent's own reports.

Candidate: for every c>1 and every x>0 a unique y>0 with the genuine Gamma ratio
Gamma(y)Gamma(y+2x)/Gamma(y+x)^2 = c, and the height h_c strictly convex on all of (0,∞);
c=2 is Remark 16(a) of Garrappa–Gerhold–Popolizio–Simon, JMAA 551 (2025) 129588. ONE family.

## Verdicts

| Gate | Verdict |
|---|---|
| FREEZE / PROVENANCE | **PASS** |
| FORMAL (my own fresh extracted strict replay) | **PASS** |
| SOURCE (actual VoR body, rendered and read by me) | **PASS** |
| MATH (independent re-derivation + own checks) | **PASS** |
| SUBSTANTIVE / NOVELTY (my own adjudication and screen) | **PASS — eligible** |
| MANUSCRIPT (all 3 pages rendered and read by me) | **PASS** |

Overall recommendation to root: **accept as outcome 2/30 additional (32/60 total), credit 1 additional**, subject to root's own acceptance prerogative. No promise was made or inherited; the verdicts above are mine. Strongest objections are stated at full strength in their own section and did not reach HOLD level.

## FREEZE / PROVENANCE — PASS

- HEAD at review start contained c0bbeeddfc; `final-review-hashes.json` binds 44 files (40 payload + manifest + packet + receipt + SUMMARY). I recomputed all 44 SHA-256 from the frozen lane bytes: **44/44 match before** and **44/44 match after** my review. The only lane-tree change visible to git afterwards is the pre-existing untracked supplementary `paper-build/` directory, which is outside the freeze.
- `git log` advanced past the freeze (root's launch commit 8c80c162d6); the bound file contents are unchanged regardless — verified by hash, not by git.
- I made my **own** byte-copy `packet-copy.zip` (SHA256 fbf9b2243a750e1fbdb219b9b163618a9f0127170af3f7cb4cd891e1ef11deff — matches the bind) plus `receipt-copy.json`, and reviewed only my copy.
- Packet: **41 entries, 40 payload + MANIFEST.json**; all 40 payload hashes recomputed from the archive: **all match**; no unexpected entries; **no prebuilt artifacts** (no .olean/.ilean/.so/.lake paths inside).
- Extracted formal sources byte-identical to the frozen lane (verified per file).
- component-bindings.json verified against the worker lane `pi-gamma-series-level-formal-r1/formal/SeriesDefect.lean` (SHA 7e6a1a36…): `diff` of the integrated file after whole-word `level_seriesTerm_nonneg → seriesTerm_nonneg` reversal is **empty — rename is the only change**. GammaEuler.lean independently declares its own `seriesTerm_nonneg`; no collision remains.

## FORMAL — PASS (my own replay, not inherited)

I ran `python3 verify_candidate.py` from **my own extraction in a fresh temp directory**; it PASSED (exit 0). I additionally verified, independently of the script's own assertions:

- Absolute Lean binary `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`: SHA256 e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550 and version string both match pins.json.
- All 8 package `git rev-parse HEAD` match pins.json; Mathlib = d13f23b723b8a846827a245b89c10fc7d3f11612; the Mathlib checkout is **clean** (no local modifications), so its dependency oleans correspond to the pinned revision.
- 9 modules compile with `-DwarningAsError=true`, empty stdout/stderr per module; 9 module logs all empty.
- My replay's `Checks.log` (e967c312…) and `audit.json` (5f840218…) are **byte-identical to the parent's** `verification/` outputs — independent two-build agreement, from a different extraction.
- **All 52 type/axiom reports read by me** from my own log: exactly 52 `'…' depends on axioms: [propext, Classical.choice, Quot.sound]` lines, set-equal to the 52 audited names (the apostrophe name `gammaHasSum'` included). No `sorry|admit|axiom|unsafe|native_decide` token anywhere in formal/ (my own grep).
- No parent/local oleans consumed: the replay temp dir starts empty and the packet contains no prebuilt artifacts; LEAN_PATH exposes only the pinned dependency packages, never a GammaLevel build directory.
- Endpoints actually inspected in the type reports: `GammaLevel.source_convexity : GammaLevel.SourceConvexity`; `source_remark16a : ∃ h, (∀ x : ℝ, 0 < x → GammaLevel.SourceLevel 2 x (h x)) ∧ StrictConvexOn ℝ (Set.Ioi 0) h`; `existsUnique_sourceLevel {c x} (hc : 1 < c) (hx : 0 < x) : ∃! y, GammaLevel.SourceLevel c x y`.
- **No-vacuity check on the actual types:** `SourceLevel c x y := 0 < y ∧ Real.Gamma y * Real.Gamma (y + 2 * x) / Real.Gamma (y + x) ^ 2 = c` (GammaDefs.lean) is the literal positive Gamma ratio; `SourceConvexity` quantifies all c>1 and all x>0 over the nonempty domain Ioi 0; the height is pinned by the genuine equation at every x>0 (the choice witness is unconstrained only off-domain, x≤0, which StrictConvexOn on Ioi 0 cannot see). `existsUnique_sourceLevel` separately certifies genuine uniqueness per (c,x). No residual series/analytic/existence/strict-anti premise: `SourceConvexity.lean` and `GammaAssembly.lean` take none — the Bohr–Mollerup HasSum bridge is closed inside `gammaHasSum'`.

## SOURCE — PASS

- `sources/jmaa-vor.pdf` SHA256 ad4b04d748016d181ca2b52f18300fcd5d305feba10901a2b20f950ddd5d03f4 (matches bind and provenance); pdfinfo confirms JMAA 551 (2025) 129588, Producer Elsevier (version of record).
- I rendered pages 12–13 **myself** with pdftoppm (150 dpi) from the packet's own copy and read both PNGs visually, cross-checked with the extracted text: Lemma 15 defines the unique y=h(x)>0 by **2Γ(x+y)² = Γ(y)Γ(2x+y)** (≡ Γ(y)Γ(y+2x)/Γ(y+x)²=2) and proves strict convexity **only on [1,∞)**; Remark 16(a) states verbatim "We believe that h is strictly convex on the whole (0,∞)…" and that its Hessian quantity H(x,y,z)>0 on (0,∞)³ (via convexity of 1/ψ′) blocks the method on the small-height interval. Exactly as the candidate's SOURCE-COMPARISON claims.
- Theorem 23 read in the body: log-convexity ⇔ α≤1 ∧ β≥h(α), log-concavity ⇔ α≥1 ∧ β≤h(α); its proof **uses h at α<1** ("1 > α > β ≥ h(α)"). The curve at x<1 is substantive, not a dead endpoint.
- arXiv abs page (fetched today): v4, 11 May 2025, is still the **latest** version; journal reference and DOI 10.1016/j.jmaa.2025.129588 match.
- The different main CBF conjectures (25/26) and the Kummer modulus question are not claimed; the accepted first-batch #23 (Simon threshold) is a different source/curve. No MathDB record for this remark is asserted, and my searches found none.

## MATH — PASS

I re-derived every step by hand from the actual module sources; independently of Lean:

1. **Bridge (finite cancellation).** g((s+m)/x) = −log(1−x²/(s+m)²) = 2log(s+m)−log(s−x+m)−log(s+x+m). The Bohr–Mollerup approximant combo logΓSeq(s−x,n)+logΓSeq(s+x,n)−2logΓSeq(s,n) cancels the `(a)·log n` and `log n!` terms **exactly** (coefficients (s−x)+(s+x)−2s=0, 1+1−2=0) and equals the n-th partial sum for every n; the limit is F(x,s)=logΓ(s−x)+logΓ(s+x)−2logΓ(s). Verified numerically to 1.6e-48 at 4 points, and certified in Lean as a genuine `HasSum`. No asymptotic hand-waving anywhere.
2. **Termwise bounds.** For m≥1: −log(1−t)≤t/(1−t) with t=x²/(s+m)² gives g((s+m)/x) ≤ x²/((s+m)²−x²) ≤ x²/m², the last since (s+m−x)(s+m+x) > m². Uniform summable majorant ⇒ convergence, continuity (continuousOn_tsum), and the zero limit at ∞. Boundary divergence: the m=0 term −log(1−x²/s²)→+∞ as s↓x dominates the nonnegative sum. IVT + strict decrease ⇒ unique level s for every log c>0. All scrutinized; no scope or convergence gap. The divergence argument in `seriesTerm_zero_ge` (the s ≤ x/√(1−e^{−M}) threshold) is algebraically exact.
3. **Strict Jensen.** Weight identity (S+m)/X = A(s₀+m)/x₀ + B(s₁+m)/x₁ with A=ax₀/X, B=bx₁/X, A+B=1 — verified **exactly over 300 random rational tuples** (ownchecks.py). g″=2(3u²−1)/(u²(u²−1)²)>0 on u>1 verified **symbolically** (sympy). Strictness even when the m=0 arguments coincide: (s₀+m)/x₀=(s₁+m)/x₁ for m=0 and m=1 forces x₀=x₁ — verified **exactly over 300 rational tuples** with x₀≠x₁. The strict gap at one index survives summation of the absolutely convergent, termwise-nonnegative-gap series (Summable.tsum_lt_tsum with summability of the weighted combination supplied). F(X,S) < log c = F(X, X+h(X)); strict decrease in the second coordinate gives X+h(X) < S; subtracting X gives the strict convexity. The Lean `by_contra` assembly in `level_height_strictConvexOn` is logically equivalent to this (I checked the antitoneOn direction and the nlinarith steps).
4. **Gamma bridge.** `logDefect_shift`/`logDefect_eq_log_iff_ratio` convert the defect level into the literal ratio via log injectivity on positives; all three Γ arguments positive. The claim's range is complete: c>1 is exactly the solvable range (ratio →∞ as y→0⁺, →1 as y→∞, strictly decreasing in y).
5. Diagnostics (not proof): h(1)=1 and h′(1)=2 match the source's anchors; slopes of h at c=2 strictly increasing on a grid spanning (0,5); series identity within a rigorous tail bound at 4 points. Recorded in `ownchecks-result.json`.

I found **no gap**. The proof nowhere differentiates the implicit curve, so the source's provably-failed Hessian route is irrelevant to it — the mechanism is genuinely different, not a patch.

## SUBSTANTIVE / NOVELTY — PASS (my own adjudication; strongest objection first)

**Strongest counter-case, at full strength:** the mechanism is one page of classical convex analysis. The Euler product for the log-Gamma ratio is classical and was available to the source authors; once written as F(x,s)=Σ g((s+m)/x), multiplying the level inequality by x gives a sum of classical perspectives composed with affine shifts, and the weighted-Jensen step is the standard perspective proof with adjusted weights; the only genuinely new-looking piece is the two-line two-shift strictness lemma. On this reading the result is a routine instantiation of a classical tool — excluded — and even the c=2 resolution of Remark 16(a) would be "routine". This is the objection I take most seriously, and I did not inherit the prior reviews' dismissal of it.

**My independent adjudication: eligible.** Reasons:
- The campaign exclusion standard (per AGENTS.md) excludes known theorems, public proofs, routine corollaries of *same-object* published results, helpers, and parameter instances. The known theorem here (perspective convexity, Rockafellar/Combettes) is **generic** — about no Gamma object, no level curves, no level radii, no shifted-lattice sums (I read the Combettes v3 claim structure as archived by the r2 reviewer and re-verified its content scope by my own reading of its abstract/props in search results; it contains no such statement). No located published theorem encodes "the level height of a convergent shifted-perspective sum is strictly convex" or performs the exact normalization xF = Σ x·g((s+m)/x) on a Gamma-ratio curve. So this is not an *equivalent corollary of a known theorem*; shortness alone has never been an exclusion criterion in this campaign (it would also exclude accepted #23).
- The source question is an explicit open **belief** in a peer-reviewed paper whose own method is **proved** in the source to fail on the missing interval; the missing interval is load-bearing in the source's own Theorem 23. This is not a wording/domain/endpoint correction and not a formalization of anything known.
- The x-multiplication/perspective identification is real: x·g((s+m)/x) is literally the classical perspective of g at (x, s+m). The preliminary reviewer's contrary "not a perspective sum" claim was wrong; the r2 correction and the current PROOF.md/paper state the mechanism correctly and credit it fully. I confirmed the corrected characterization myself from the module sources; no residual overclaim remains in the reviewed bytes.
- All-c>1 is ONE family with a single uniform proof; helpers, the known x≥1 case, and classical tools receive no credit anywhere in the reviewed manuscript/PROOF.

**My own fresh bounded screen (access limits recorded):**
- **Citation graph** (Semantic Scholar API, public read): arXiv:2410.11852 has **4 citing papers** — q-fractional integral operators (2610.10574), fractional Schrödinger controllability (2602.07514), a fractional telegraph backward problem, and derivatives of ML functions. I fetched the abstracts of the two arXiv ones: **none** touches h, Lemma 15, or Remark 16(a). Ferreira–Simon 2512.04940 (known nearest neighbor) re-confirmed off-topic (convex ordering of E_α).
- **Registry** (trureturing mdbook, public read): for this paper only the **Kummer modulus question (Remark 6)** is tracked (refuted 2026-10-26 by a different construction). **No record on Remark 16(a)/h-convexity.** No MathDB record for this remark was found or is asserted.
- **Primary-genre screen** (web search): gamma-ratio convexity genres (Merkle-type F/G, geometric convexity, log-concavity of gamma series, complete monotonicity of ratios), level-set convexity literature (PDE Green-function genres), perspective-function literature, and a 2026 Springer paper on concavity structure/zeros of ML functions (Li–Morgan–Siegrist — fractional ODE inflection points, different problem). **No prior resolution of Remark 16(a) and no subsuming strict level-radius theorem found.**
- **Limits:** no MathSciNet/zbMATH/Scopus/Web-of-Science crawl; Orlicz-means and harmonic-mean literature only partially screened; empty results are not proof of absence; no worldwide priority claimed or needed. No 429/403 encountered (I avoided protected endpoints; all fetches were public reads).

## MANUSCRIPT — PASS

- `paper.pdf` SHA 659dcd01cc… matches the bind; 3 pages; I rendered all three myself (110 dpi) and read them visually.
- Theorem 1 states exactly the full formal claim: for c>1, unique h_c(x)>0 satisfying the literal ratio, plus strict convexity for all distinct x₀,x₁ — matching `SourceConvexity` + `existsUnique_sourceLevel`, including uniqueness. Section 3 states zero discovery credit, pending final review and acceptance, standard-3 axioms, Lean 4.34.1 / Mathlib d13f23b723b, 52 declarations — all consistent with the verified facts.
- No implication to the source's complete-Bernstein conjectures or other ML questions; the classical tools (perspective, Combettes Props 2.3/2.13, Euler product, Jensen) are explicitly credited and disclaimed as non-new.
- Bibliography correct (GGPS with DOI and arXiv v4 pointer; Combettes arXiv:1610.01552v3). Build log: **0 Overfull, 1 Underfull** (badness 1122, bibliography lines 155–158 — cosmetic), matching paper-qa.json.
- Formulas checked against the formal modules: the weight identity (5), the Jensen inequality (6), the bound (4), and the strictness argument match `StrictJensen.lean`/`SeriesDefect.lean`; the series identity (3) matches `GammaEuler.lean`'s closed HasSum bridge.

## Gaps and honest limits (non-blocking)

1. Novelty screen is bounded (above); an unlocated published subsumer can never be fully excluded.
2. The routine-ness objection is a standing judgment call at the boundary of the campaign standard; my adjudication is recorded above with reasons, not as a decree.
3. All numerics in my lane are diagnostics, not interval certificates; the proof burden is carried by the Lean kernel plus my hand re-derivation.
4. `paper-build/` in the parent lane is untracked supplementary material outside the 44-file freeze (build log only); it does not affect the bound artifact.

## Provenance of this review

All artifacts in `lanes/pi-gamma-level-final-review-r1/` only: `packet-copy.zip`, `receipt-copy.json`, `replay/extracted/**` (my own extraction + replay outputs copied to `checks/`), `renders/vor-12.png, vor-13.png, paper-{1,2,3}.png` (my own renders), `ownchecks.py`, `ownchecks-result.json`, `review.md`, `provenance.json`. Public read-only network access only (arXiv abs, Semantic Scholar API, trureturing mdbook, web search). No git, no staging, no commits, no shared/parent edits, no external messages or uploads, no access-control bypass. Frozen lane 44/44 verified unchanged before and after.
