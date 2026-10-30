# Preliminary adversarial review — one combined quartic counterexample (Lachaume Conj. 1 & 3)

Reviewer: pi (subagent, independent). Date 2026-10-26. Parent candidate frozen commit fea5692b66 (lane `parent-lachaume`). Scope: source fidelity, full mathematics, SERIOUS bounded novelty. Not a formal/paper review (none exists). Credit 0 here; this review is not counted in any tally. ONE construction — Conj.1 and Conj.3 refutations share the same quartic and are not counted separately.

**Gate summary: Source fidelity PASS. Mathematics PASS. Novelty PASS (bounded), with one decisive objection that changes the required novelty scoping (MathOverflow 248816 was missed by the parent screen and must be integrated). Overall: HOLD for integration of the MO citation and re-scoped novelty statement; no gate FAIL.**

---

## 1. Source fidelity — PASS

- I personally re-downloaded arXiv:1712.10327 (PDF) and the abs page. SHA-256 of my fresh copies **exactly match** the parent's frozen hashes (`7b27f885…` pdf, `156d76c8…` abs). Submission history shows **v1 only** (12 Dec 2017); no v2.
- **Visual inspection of rendered PDF p.3**: definitions f_a = a₀+a₁σ₁+…+a_pσ_p on Γ_n; f̄_a = f(X,…,X) = Σ a_k C(n,k) X^k; sets K, X, Ξ; **Conjecture 1** literally: f_a is 1/p-concave on Γ_n ⟺ f_a 1/p-concave on Δ ⟺ f̄_a 1/p-concave on ℝ*_+. Γ_k = {σ_i(y)>0 ∀ i≤k}, Γ_n = (ℝ*_+)ⁿ, Δ = {(t,…,t): t>0}. All match the parent's reading.
- **Visual inspection of p.5**: **Conjecture 3** literally: P ∈ ℝ₊[X], deg P = n; "P is real-rooted ⟸ PP″ + (1/n − 1)P′² ≤ 0 **on ℝ**". Definition 2.1: (P1) real-rooted; (P2) the differential inequality on ℝ; (P3) P^{1/n}-concave on ℝ*_+; Prop. 2.2 proves (P1)⟹(P2)⟹(P3); Theorem 2.4 proves the conjecture for deg P ≤ 2, and (P1)⟺(P2) for deg 3. Our degree-4 example is exactly the first unproven degree — consistent with the paper, no internal contradiction.
- **Source examples checked**: Theorem 2.11/2.12 (Kurtz 1992, ref [14]) are sufficient conditions, not counterexamples; the n=2 worked example (a=(1,p,q)) concerns p=2 only. No example in the paper contradicts or anticipates ours.
- **Author's later paper** (arXiv:1712.04528 = "The constraint equations of Lovelock gravity theories", = JMP 59 (2018) 072501): I read the full text. Theorem 2.7(a–d) gives only **sufficient** criteria (incl. (d) Walsh/real-rooted diagonal ⟹ K_n^p). **No counterexample to Conjectures 1 or 3 anywhere; no hypothesis revision.**
- **2017 thesis** ("Des équations de contrainte en gravité modifiée", Tours, defended 15 Dec 2017; INSPIRE copy downloaded): chapter 5 restates Conjectures 1 and 3 **identically** (no revised hypotheses), proves Conj. 3 for deg P = 2, 3 only, and contains **no contre-exemple** (grep across all 193 pages: none).
- **MathDB**: fresh API pulls of 338076–338079. 338076 ("diagonal concavity conjecture", = Conjecture 1): status open, `solutions: []`, `comments: []`, `progress: null`, `model_attempts: []`, `human_solves: []`, `replies: []` — matches parent snapshot byte-for-byte. 338077/78/79 are Conj. 2 / 4 / 5 respectively — **distinct assertions, correctly not claimed**. Conjecture 3 has no MathDB record, as the parent says.
- **Carptopus** (v0.1-beta 4 Sep 2026, DOI 10.5281/zenodo.22299983): live README and .tex from GitHub are **byte-identical** to the parent's frozen copies. It proves Conjectures 4 and 5, notes 4⟹2 via Lachaume Thm 2.7(d), and states verbatim: "These implications do not address Lachaume's Conjectures 1 or 3." No conflation risk if cited as the parent does.

## 2. Mathematics — PASS (independent rederivation, different code path)

My own sympy-based script (`review-verify.py`, output in `commands/review-verify-output.txt`; distinct from the parent's pure-`fractions` path). All checks exact, not floating-point:

1. **Identity**: 4PP″ − 3(P′)² = −144(x²−1)², verified by symbolic expansion to 0. Hence PP″ + (1/4−1)P′² = −36(x²−1)² ≤ 0 **on all of ℝ** — Conjecture 3's hypothesis (P2) holds literally, globally. Robust to any reading of "on ℝ" (even restricted to {P>0} it holds).
2. **Roots**: P(x) = (x²+(4−2√3)x+1)(x²+(4+2√3)x+1) verified; z = √3−2+i√(4√3−6) is an exact root with positive imaginary part (√(4√3−6) > 0 since √3 > 3/2). Exact roots: −2−√3 ± √(6+4√3) (real, negative) and −2+√3 ± i√(4√3−6). So (P1) fails. **Refinement of the parent's claim found by this review**: P is *not* positive on all ℝ (its two real roots are negative, ≈ −0.136 and −7.33); P > 0 precisely for x > −2−√3+√(6+4√3) ≈ −0.136, in particular on **all of x > 0** — exactly the parent's stated claim, which is correct and sufficient for (P3) on ℝ*_+ (h″ = −9(x²−1)²/P^{7/4} ≤ 0 there).
3. **Diagonal**: with a = (1,2,1,2,1) in n = 4 variables, f_a(t,t,t,t) = 1+8t+6t²+8t³+t⁴ = P(t) exactly (verified symbolically). So f̄_a = P and (P3)/diagonal-concavity holds on ℝ*_+; a ∈ X_4^4.
4. **Literal f values**: g(t) = f_a(2,t,t,t) = 5+12t+15t²+4t³ (symbolically verified); f(2,1/20,1/20,1/20) = 2819/500; f(2,1/10,…,1/10) = 3177/500; f(2,3/20,…,3/20) = 7151/1000 — all exact matches.
5. **Rational witness chain** (all exact rational comparisons): (15409/10000)⁴ < 2819/500; 3177/500 < (15877/10000)⁴; (16352/10000)⁴ < 7151/1000; 15877/10000 < (15409/10000 + 16352/10000)/2, gap exactly 7/20000. Hence f(c)^{1/4} < (f(a)^{1/4}+f(b)^{1/4})/2 at strictly positive inputs — a strict midpoint-concavity violation of f_a^{1/4} on Γ_4 (all coordinates > 0, f_a > 0 on Γ_4 since a_k > 0, σ_k > 0). Conjecture 1's ⟸ direction fails. Numeric magnitudes: 1.54092417, 1.58767572, 1.63527838; violation ≈ 4.26×10⁻⁴.
6. Consistency: the slice curvature 4gg″−3g′² = 168−240t−612t²−240t³−48t⁴ is > 0 near t = 0.1 (parent's "intuition only" value 168 at t=0 verified), consistent with the witness; not needed for the proof.

No errors found. The mathematics is correct and complete at the level of a standard exact-arithmetic verification.

## 3. Serious bounded novelty — PASS with decisive objection

**DECISIVE OBJECTION (integration required): the parent screen missed MathOverflow question 248816** (asked by "LacXav" = Lachaume, 1 Sep 2016, i.e. *before* the paper): "Is it true that P has only real roots ⟺ PP″+(1/n−1)P′²≤0? … what if P has only nonnegative coefficients?" This is the closest public prior for Conjecture 3 and the parent's `provenance.json`/PROOF.md do not mention it. Two answers exist:
- Gjergji Zaimi: **P(x) = x⁴−1** satisfies PP″+(1/4−1)P′² = −12x² ≤ 0 on ℝ and has nonreal roots. Also P = x⁵−x. **Mechanism-relative prior**: 4(x⁴−1)(12x²) − 3(4x³)² = −48x² — the same "exact negative-identity" mechanism as our −144(x²−1)².
- Fedor Petrov: root-configuration family (i, −i, 1^m, 0^m).

**Why this does not kill novelty (scoped)**: both prior examples have negative/alternating coefficients and neither is in ℝ₊[X]; the asker's nonnegative-coefficient addendum received **no answer**. Moreover x⁴−1 is negative on (0,1), so it cannot serve Conjecture 1 (whose diagonal condition needs f̄_a > 0 and 1/p-concave on all of ℝ*_+, with a ∈ (ℝ₊)^{p+1}); our P is positive on all of ℝ*_+. Nor can Zaimi/Petrov examples be trivially shifted into ℝ₊[X] (the differential condition is not translation-invariant).

**Required re-scoping of any novelty claim**: the bare statement "the converse of the Cauchy–Schwarz implication fails" is **prior art (2016)**. What is candidate-new: (i) a **nonnegative-coefficient** counterexample answering Conjecture 3 as literally stated in the paper/thesis (and leaving (P2)⟹(P3) intact — our P is 1/4-concave on ℝ*_+); (ii) the **combined** refutation of Conjecture 1 (diagonal-concavity ⟹ global concavity for σ-sums) via the same quartic; (iii) minimality-adjacent fact: degree 4 is the first degree not covered by Lachaume's Theorem 2.4. Any write-up must cite MO 248816 and position against x⁴−1 explicitly.

**Other novelty checks performed**: Semantic Scholar citation graph: exactly 2 citations of 1712.10327 — the author's own Lovelock/JMP paper (read in full: no counterexample) and Andrica–Rădulescu, "Some New Methods for Generating Convex Functions" (Springer, 2019/2020) — a general convexity-methods survey (paywalled; abstract/TOI-level check only, no counterexample indicated). Web searches for the explicit quartic, "Lachaume conjecture" resolutions 2020–2026, normalized-Laguerre converse counterexamples, and fourth-root-concave polynomials with nonreal roots: nothing that resolves Conj. 1 or 3. Carptopus explicitly excludes 1/3. MathDB 338076 open with all arrays empty. INSPIRE page is JS-rendered (fallback check via search snippets only). No evidence of prior public existence of this quartic or mechanism in ℝ₊[X].

**Access/coverage limits (candid)**: no Google Scholar full sweep; no MathSciNet/Zentralblatt; Andrica–Rădulescu full text paywalled; INSPIRE citing-works list read only via search snippets; MathDB searched by known post ids, not by full-text search; the 2026 Carptopus PDF (vs. repo tex) not separately downloaded; possible non-indexed 2026 preprints (Zenodo/figshare/RePEc) only partially covered. These are bounded-screen limits, not a certificate of global novelty.

## 4. Gate decisions

| Gate | Decision |
|---|---|
| Source fidelity (literal hypotheses, versions, MathDB, Carptopus, thesis, JMP) | **PASS** |
| Full mathematics (identity, roots, diagonal, Jensen witness, rational bounds) | **PASS** |
| Bounded novelty | **PASS, conditional** on integrating MO 248816 and re-scoping the claim as above |
| Formal/Lean, manuscript, packet | **NOT REVIEWED / ABSENT** (out of scope, correctly not claimed) |

**Overall: HOLD** — the construction is mathematically sound and, properly scoped, appears genuinely new; but the parent lane must (1) add MO 248816 as the closest public prior (2016, by the author himself), (2) explicitly distinguish our ℝ₊[X] example from Zaimi's x⁴−1 (mechanism-relative prior), and (3) drop any phrasing implying the unconstrained converse was open. No absolute priority claims anywhere.

## 5. Artifacts in this lane

- `review.md` — this review.
- `provenance.json` — provenance for this review.
- `review-verify.py` + `commands/review-verify-output.txt` — my independent sympy verification (all exact checks).
- `sources/arxiv-1712.10327-fresh.pdf`, `arxiv-abs-fresh.html`, `fresh-1712.10327.txt`, `p3-03.png`, `p5-05.png` — fresh primary (hashes match parent freeze); visual inspection renders.
- `sources/lovelock-1712.04528.pdf`, `lovelock.txt` — author's JMP 59 (2018) 072501, full text read.
- `sources/lachaume-thesis-2017.pdf`, `thesis.txt` — 2017 thesis, full text read.
- `sources/mathdb-338076…338079-fresh.json` — fresh MathDB pulls (all arrays empty on 338076).
- `sources/carptopus-readme-live.md`, `carptopus-main-live.tex` — live repo copies, byte-identical to parent freeze.
- `sources/mo-248816.html` + `commands/` — MathOverflow 248816 snapshot (the missed prior).
- `commands/sha256-lane-sources.txt` — checksums.
