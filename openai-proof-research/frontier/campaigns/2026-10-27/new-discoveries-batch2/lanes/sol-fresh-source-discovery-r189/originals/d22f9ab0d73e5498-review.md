# Independent review — candidate `classical-means` (MathDB 338823)

Reviewer: pi-means-review lane (independent GLM review sub-agent). Commit reviewed: `88c5c34a011ca45d1378cb332ee5d3fd6eca0487`.
Candidate: complete real-exponent classification of the four classical means, refuting Meštrović–Andjić Conjecture 1.5 (published) / Conjecture 1.6 (arXiv v1) on the interval 1/2 ≤ n < 1.

**Verdict: PASS on all four gates. No decisive objection found. No prior solution found.**

---

## Gate 1 — Exact source review: PASS

I personally viewed the publisher PDF (SHA-256 `e80be06161e9dc04d3c8f02a967c083086dd3220aa8e03dcd50048fce9d7c232`, verified locally) as rendered pages, all seven pages, including pp. 1891, 1892, 1893, 1894, 1895, 1897 content:

- **p. 1892**: exact definitions H = 2xy/(x+y), G = √(xy), A = (x+y)/2, Q = √((x²+y²)/2) for positive x,y — literally identical to the Lean `arithmetic/geometric/harmonic/quadratic`. Theorem 1.1 proves A·G ≥ Q·H and A^n+G^n ≤ Q^n+H^n **for integer n only** (induction); Remark 1.4 poses the real-exponent question.
- **p. 1894, Conjecture 1.5 (verbatim)**: "The inequality (4) holds for all negative real numbers n and for all positive real numbers n greater than or equal to 1/2. Moreover, none of the inequality (4) or its converse inequality holds true for each real number n in the interval (0, 1/2)." Inequality (4) is A^n+G^n ≤ Q^n+H^n.
- **p. 1895**: proof of Theorem 1.1 via Lemma 2.1 (integer induction) and Q−G ≥ A−H; no real-exponent content.
- **arXiv:1804.00542v1** (fetched 2026-10-26): Conjecture 1.6 verbatim identical to published Conjecture 1.5 (renumbered). Abstract confirms integer-n result only.

The candidate's characterization of the source is exact: the source asserts validity on [1/2, ∞) ∪ (−∞, 0) and "neither direction" on (0, 1/2); it proves nothing for non-integer n. The candidate's classification (valid iff n ≤ 0 or n ≥ 1; converse iff n = 0) confirms the n < 0 clause, refutes the source's entire asserted validity interval [1/2, 1) (a substantive interval failure, not endpoint wording), proves the "neither" clause on (0, 1/2) and extends it to (1/2, 1), and adds the trivial n = 0 equality (consistent with the source's "negative" phrasing; no conflict).

**MathDB 338823 live retrieval** (`https://mathdb.com/api/posts/338823`, 2026-10-26, saved `sources/mathdb-338823-live.json`, SHA-256 `999e3cc9d98db1b8dcbdda540226542f78bedc6690e294558a8e01ca853dd090`): UUID `d0d7b2e3-8f6a-49ce-b353-d1c8d4e85ee8`, status `open`, and **all** of `solutions`, `human_solves`, `model_attempts`, `replies`, `comments`, `formulations`, `attachments` are empty and `progress` is null. Field-by-field comparison with the candidate's snapshot `sources/338823.json`: all checked fields MATCH. No posted resolution exists (I specifically checked every solution-bearing array, avoiding the previously-rejected miss pattern).

## Gate 2 — Mathematical proof: PASS

- **Sufficiency (n ≥ 1 and n ≤ 0)**: from AG = QH, A+G ≤ Q+H (both reproved from literal definitions in Lean) plus two-point convexity of t ↦ t^n (n ≥ 1) and increasing-convective exp/log majorization (n ≤ 0). Classical tools, correctly applied; explicitly credited as classical by the candidate.
- **Necessity (0 < n < 1)**: normalization G=1, A=c≥1 with actual inputs x = c±√(c²−1) > 0, H = 1/c, Q = √(2c²−1); defect D_n(c) = Q^n+H^n−A^n−G^n has D(1)=D′(1)=0, D″(1)=4n(n−1) < 0, so D_n < 0 just right of 1 — actual-input failure for every 0<n<1.
- **Explicit half-power witness**: x = 4+√15, y = 4−√15 gives A^{1/2}+G^{1/2} = 3 and Q^{1/2}+H^{1/2} = 31^{1/4}+1/2 ≈ 2.8596; 3 > 2.8596. Independently verified numerically.
- **Converse (n ≠ 0)**: n>0: ε=(5/4)^n−1, c = max(2,(2/ε)^{1/n}) ⇒ Q ≥ 5c/4, εc^n ≥ 2 ⇒ Q^n > c^n+1 = A^n+G^n (strict, plus H^n > 0). n<0: c = max(2, 3^{1/(−n)}) ⇒ H^n ≥ 3, A^n ≤ 1, Q^n > 0. At n = 0 equality. All sound.
- **Independent numerical check (mine, 50,000 random positive pairs per exponent)**: original direction valid exactly at n ∈ {−2,−1,−0.5,0,1,1.5,3} and violated at every sampled n ∈ (0,1) including 0.5, 0.75, 0.9, 0.99; converse violated at every sampled n ≠ 0 (e.g. n = −2, −1, −0.3, −0.01, 0.3, 0.5, 0.99, 1). Matches the claimed classification exactly.

No gap found. Real-power domains (positive bases throughout; rpow on ℍ-positive bases), derivative-neighborhood signs, strict positivity of inputs, the reciprocal inequality H = 1/c, and the n = 0 case are all handled.

## Gate 3 — Complete formal scope / independent replay: PASS

I copied all five frozen modules, `candidate.json`, `verify_candidate.py` and `pins.json` from commit `88c5c34a01` into my own lane (`replay/`) and confirmed SHA-256 of all five `.lean` files equal the stated frozen hashes (and equal the working tree):

- MeanAlgebra `e0665a9e…`, MeanSufficiency `f93c74c8…`, MeanNecessity `6cca1827…`, MeanClassification `e5f3eeec…`, MeanConverse `6199e057…` — all match.

Fresh strict replay executed by me (not the parent's log): Lean **4.34.1** (`…/lean-4.34.1-linux/bin/lean`), mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` with all dependency revisions verified against `pins.json`, `warningAsError=true`, forbidden-token scan (sorry/admit/axiom/unsafe/native_decide) clean. Result: **PASS, 34 declarations** (10+5+8+6+5), receipt at `replay/build/verified/audit.json`.

I inspected the generated `Checks.log` myself: every one of the 34 declaration types printed, including the five main theorems with exactly the claimed statements:
- `source_full_classification (n) : (UniversallyValid n ↔ n ≤ 0 ∨ 1 ≤ n) ∧ (ConverseUniversallyValid n ↔ n = 0)`
- `source_exponent_classification`, `source_converse_exponent_classification`, `source_failure_all_intermediate`, `explicit_half_power_failure : ¬ SourceComparison (1/2) (4+√15) (4−√15)`.

`SourceComparison` uses the literal mean definitions and the source's direction A^n+G^n ≤ Q^n+H^n. All witnesses use actual strictly positive inputs (`normalized_pair` proves 0 < pairLeft/pairRight). Axiom report on every declaration: only `propext, Classical.choice, Quot.sound`; no `sorryAx`, no new axioms. The final theorems carry no leftover derivative/normalization/witness hypotheses.

## Gate 4 — Bounded novelty: PASS (bounded)

Searches performed (2026-10-26; all saved in `sources/` search records via responseIds noted in provenance.json): exact title/authors; conjecture-number resolution queries; "1804.00542" counterexample queries; power majorization between classical means; sums-of-powers/majorization literature; √A+√G vs √Q+√H; RGMIA; Sándor's survey; Jameson Monthly 2022/2023; Meštrović 2024–2026 follow-ups.

Findings:
- **Zero citations** of the source: Springer/Scifaro metadata "0 citations", Semantic Scholar API `citationCount: 0, citations: []`, Crossref `is-referenced-by-count: 0`. No published resolution or refutation found anywhere.
- **Meštrović, "A chain of eight inequalities…", Teach. Math. XXVII(1) 2024** (fetched full PDF): integer/square powers only; does not cite or mention the conjecture; no real exponents.
- **Phuc & Thuy, Teach. Math. XXIX(1) 2026** (nested-means poset): cites only the 2024 chain paper; unrelated to real-exponent classification — corroborates that the conjecture remained open through 2026.
- **Jameson, Amer. Math. Monthly 130(3) 2023, 276–278**: compares M_p with (1−p)G + pA — a different comparison; does not supply ours (nearest-miss recorded).
- **Sándor, "Theory of Means and Their Inequalities"**: collected conjectures are of different form (means of n arguments, not power sums of the four two-argument means); no citation of the source.
- **Power-majorization literature** (Clausing; sums-of-powers counterexamples): general n-vectors; no theorem giving this two-point family's exact iff exponent range.
- No existing theorem was found that directly supplies the full classification or the counterexample; the classical two-point convexity/majorization ingredients used for sufficiency are old and are explicitly credited by the candidate. The discovery is one outcome: the explicit resolution of Meštrović–Andjić Conjecture 1.5/1.6 — validity exactly on n ≤ 0 ∪ n ≥ 1, refutation of the asserted 1/2 ≤ n < 1 interval, converse validity exactly at n = 0.

**Novelty is bounded, not absolute**: empty searches are not proof of worldwide priority. Recorded access limits below.

## Access limits

- MathSciNet and zbMATH: no institutional access; not consulted. (zbMATH Open web search returned nothing relevant via general search.)
- Jameson (Monthly 2023) full text: HTTP 403 (paywalled); content known from abstracts/snippets — different comparison.
- Sándor survey PDF: only first ~100 of 569 pages extractable; the remainder unchecked (recorded as a limit, low relevance).
- Google Scholar "cited by" not directly accessible; substituted by Semantic Scholar API + Crossref + Exa metadata, all agreeing on 0 citations.
- MathDB: live full post retrieved; no access limits.

## Objections

None decisive. Two minor notes, neither blocking:
1. The n = 0 point is added beyond the source's "negative n" phrasing; it is the trivial equality 2 = 2 and is folded into the single classification, not a separate claim.
2. The sufficiency half is elementary classical material; the candidate correctly does not claim it as novel and counts ONE outcome total (no credit for integer cases, witnesses, helpers, or the reverse classification separately).

## Recommendation

- Exact source: **PASS**
- Mathematical proof: **PASS**
- Complete formal scope/replay: **PASS**
- Bounded novelty: **PASS** (new explicit source resolution; priority not certifiable beyond searched sources)

Eligible to be counted as 1 of 30 (one outcome). Acceptance and discovery-count updates remain the parent's action; this review does not change them. No manuscript exists; none authored by me.
