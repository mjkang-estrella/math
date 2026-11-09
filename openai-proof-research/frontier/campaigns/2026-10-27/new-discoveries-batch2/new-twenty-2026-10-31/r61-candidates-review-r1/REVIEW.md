# r61-candidates-review-r1: independent adversarial review of MathDB 366834 and 366371

This is a review, not an acceptance. It earns zero credit, and root alone accepts. The campaign count is unchanged at 7/20 beyond 39. All work was done by Claude Opus 5.5 with no child agents, on 2026-11-01.

## Verdicts at a glance

| ID | A source | B math | C Lean | D prior art | E significance | Overall |
|----|----------|--------|--------|-------------|----------------|---------|
| 366834 caterpillar centre | QUALIFIED_PASS | PASS | PASS technically; target QUALIFIED | PASS (bounded) | QUALIFIED_PASS | **HOLD** |
| 366371 ordinal majorization | PASS | PASS | PASS | PASS (bounded) | QUALIFIED_PASS | **QUALIFIED_PASS** |

Machine-readable detail is in `review.json`.

## Integrity

- Read-only inputs: all 251 files under `../expanded-corpus-r61` were hashed before and after. The two hash lists are identical (sha256 of the list: c11d2c8a…2702). See `receipts/input-hashes-{before,after}.txt`.
- Lean: both proof files were re-extracted into `fresh/` (same sha256 as the lane's). Each was built with `lean -j1 -DwarningAsError=true -o` (exit 0, empty logs) and then checked with `leanchecker` (exit 0).
- The rebuilt oleans are byte-identical to the lane's: bfc2f6d1… and cddbfa4e….
- Audit: my own all-local-declaration audit (`fresh/RevAudit*.lean`, logs in `logs/audit-*.log`) covers 52 constants for CaterpillarCenter and 95 for OrdinalLine, generated ones included. For each constant it checks:
  - module origin, kind and full type;
  - that every def and theorem has a value, and that no value contains sorry;
  - that there are no axiom or opaque declarations;
  - that nothing is unsafe, partial, implemented_by or extern;
  - that transitive axioms are only `propext`, `Classical.choice` and `Quot.sound`.
- Both audits print AUDIT_OK. The endpoint statements are printed in `logs/statements.log`.
- Resource caps: every process ran through `scripts/limited.py` (2 CPUs, CPU 120 s, wall 140 s, private RSS 6 GiB). No background jobs remain.

---

## MathDB 366834: caterpillar maximum-centre conjecture

### A. Source fidelity (QUALIFIED_PASS)

The survey text is verbatim identical in arXiv 2501.16144 v1, v2, v3 and v4. I fetched all four and compared them:

> If T is a caterpillar, r ≥ 1, and z is a maximum r-center, then the neighbor of z has maximum degree.

It appears right after ZRH's theorem that, in the caterpillar P^{k,t}, every pendant neighbour of v₂ or v_{k−1} is a maximum r-centre for all r. Those are vertices of maximum degree. The subsection has no r ≤ μ/2 restriction anywhere.

I could not obtain the original Zhang–Ran–Huang wording. I tried, each once, with receipts in `sources/`:

- ScienceDirect abstract page: 403, not retried.
- zbMATH Open 1529.05125: review text withheld for licensing reasons.
- OpenAlex and Semantic Scholar: no abstract, closed access, no arXiv version.
- The only other citer, Zhang–Zhang (Disc. Math. 2026): no arXiv version.

A search-engine snippet of the publisher abstract calls the conjecture "Conjecture 4.1" and says the paper settles centres for three caterpillar types. That is unverified secondary text.

The scope risk is confirmed and is sharper than the brief suggested. The literal universal reading fails **in range** at r = 2 on the authors' own P^{4,1} (μ = 4):

- every leaf is a maximum 2-centre;
- the leaves at v₁ and v₄ hang off degree-2 vertices, while Δ = 3.

So the only non-trivial reading is existential: some maximum r-centre is a leaf adjacent to a maximum-degree vertex. Credit can rest only on refuting that reading.

### B. Mathematics (PASS), with my own exact re-verification

Method (`scripts/cat_verify.py`): brute-force enumeration and independence-polynomial tree DP agree on every star. μ is computed by an independent-domination tree DP and agrees with brute force for n ≤ 19.

**The 11-vertex witness, leaf counts (1,2,1,0,2):**
- α = 7, μ = 4, Δ = 4.
- Stars at r = 6: 7, 1, 2, 12, 0, 8, 13, 13, 12, 14, 14.
- The maximum centres are exactly {9, 10}, adjacent to v₄ of degree 3.
- Both readings fail. But r = 6 > μ/2 = 2, so this witness is outside the Holroyd–Talbot range.

**Minimality.** An exhaustive search confirms there is no existential failure with 3 ≤ r ≤ α for n ≤ 10. The unique failure at n = 11 is (1,2,1,0,2), up to reversal.

**The family (m−1, m, m−1, 0, m) at r = 5.** It fails the existential reading for every m = 3..10.

- μ = m + 3 exactly. This is checked by DP, by brute force for m ≤ 4, and by hand: a spine vertex outside S forces all its leaves into S, and the cheapest spine choice is {v₀, v₂, v₄}.
- Correction to the root diagnostic: m = 7 has **31** vertices (μ = 10, Δ = 9, maximum centres = the 7 leaves of v₄, of degree 8). The 35-vertex graph is m = 8 (μ = 11, Δ = 10, neighbour degree 9).
- Both are exact in-range counterexamples (2r = 10 ≤ μ). m = 7 is the first in-range member.

**Smallest in-range witnesses found** (`scripts/cat_search.py`):
- Exhaustive over all caterpillars with n ≤ 23: no failure with 3 ≤ r ≤ μ/2.
- n = 24 to 27, spine length ≤ 7 only: none.
- n = 28: (1,4,6,5,0,6) at r = 5 (μ = 10). The maximum centres are the 6 leaves of v₅, of degree 7, with star 10857. The leaves of the unique degree-8 vertex v₂ have star 10853.
- n = 28: (3,4,5,4,1,5) at r = 6 (μ = 12).
- Both n = 28 cases were cross-checked by brute force.
- The minimum in-range order therefore lies between 24 and 28.

### C. Lean (technically PASS; the target needs strengthening)

The definitions are faithful:
- `IsCaterpillar` is a tree plus a dominating path.
- `starSize` counts independent r-sets containing v, via `IsNIndepSet`.
- `IsMaxCenter` takes the maximum over all vertices.

How the two endpoints relate to the scope:
- `not_caterpillarCenterConjecture` is the exact negation of the literal statement. That statement is trivially refutable at r = 2, so this endpoint carries no significance on its own.
- `not_caterpillarCenterConjectureWeak` negates "∃ maximum centre with some neighbour of maximum degree". That is the meaningful theorem, and it is proved. But neither endpoint has r ≤ μ/2.

**Recommended target** (full text in `review.json`): `¬ ∀ caterpillar T, ∀ r ≥ 1, (every maximal independent set has ≥ 2r elements) → ∃ z, IsMaxCenter T r z ∧ ∃ w, T.Adj z w ∧ T.degree w = T.maxDegree`.

- Use the n = 28 or n = 31 witness. This one endpoint implies both existing endpoints.
- Feasibility: raw kernel `decide` over the Finset definition is out of reach. A probe counting one 3-star on the 28-vertex graph (3,276 subsets) exceeded the 6 GiB private-RSS cap after 28.6 s (`fresh/Probe3.lean`, `logs/probe3.receipt.json`).
- A proved counting method is needed: either a computable List.rec counter with a correctness bridge to the Finset card, or a forest product formula for i_{r−1}(T − N[z]).
- The μ ≥ 10 bound has a short structural proof.
- Estimate: a few hundred lines, medium risk.

### D. Prior art (bounded PASS)

- Survey v4 (August 2026) still lists the conjecture as open, along with Problem (b) on where the maximum centres of caterpillars lie.
- Estrugo–Pastine (2021) predates ZRH.
- arXiv 2601.16953 (perfect r-ary trees) was read and is irrelevant.
- Two web searches found no refutation.
- OpenAI/math HEAD is unchanged at 4eaee875…. The Omega HEAD is now fae0c9c9…; its HEAD commit touches one unrelated theory doc, and the intermediate commits were not enumerated (HEAD-only rule). Keyword screens found nothing.
- Residual: the bodies of ZRH and Zhang–Zhang 2026 are unread.

### E. Significance (QUALIFIED_PASS); overall HOLD

- This is a genuine refutation of a published 2024 conjecture that a 2025/2026 survey lists as open, **provided** the existential reading is what gets credited.
- The literal failure alone is a wording defect and is worth zero.
- The witness is small and computer-found, so the result is modest.

The HOLD is about scope and endpoint, not mathematics:
1. Formalize the in-range existential endpoint.
2. Root should rule that the existential reading is the intended exact scope of a record whose literal wording is trivially false.
3. Residual risk: the unread original may restrict to a caterpillar subclass, which no witness can pre-empt.

---

## MathDB 366371: Keller–Petrov Conjecture 7.4

### A. Source fidelity (PASS)

I read Definition 1.1 (i)–(vii), (7.1)–(7.3), I_n, Definition 7.1, Proposition 7.2, Conjecture 7.4 and Theorem 7.5 in the arXiv HTML. The Lean definitions match:

- **IsOrdinalSpace** matches the axioms field by field.
- **EmbeddableInLine** matches (7.1)–(7.3) with |s − t|.
- **Prec and Sim** use one permutation π of {1..k}, the same k on both sides, and "not (7.4)" taken for that same π.
- **HasMajorization** quantifies over all k > 0 and all pairs of monotone tuples (repeats allowed) for the given enumeration.
- **The conjecture** reads "there exists an enumeration", rendered in Lean as a universally quantified hypothesis, which is equivalent.

The two readings of "but not (7.4)" are "not all equal under this π" and "not I ∼ J". I checked them literally for k ≤ 4 and they coincide. In general they agree because δ is a total preorder.

On the range left open: the source says sufficiency is unknown "if n > 5" but proves it only for n ≤ 4, so n = 5 is formally unaddressed. The witness has n = 6, which is open under either reading.

**New finding:** the paper is not a 2024 preprint. It was published in *Acta Math. Hungar.* 160 (2020) 119–152 (received February 2019, online 5 September 2019; Springer landing page and OpenAlex). The arXiv v1 dates from December 2024. Springer showed institutional (UC Berkeley) access, which is not public, so I did not download the full text. That the published Conjecture 7.4 matches the arXiv version is therefore assumed, not verified.

### B. Mathematics (PASS), with my own re-verification (`scripts/ord_verify.py`)

- The pair ranking reproduces the Lean matrix D exactly.
- Axioms (i)–(vii) hold by brute force over all 6⁶ sextuples.
- **Literal Definition 7.1** (repeats, explicit permutations), k = 1..4:

  | k | chain pairs | strict-majorized pairs | violations |
  |---|-------------|------------------------|------------|
  | 1 | 441 | 195 | 0 |
  | 2 | 3,136 | 1,192 | 0 |
  | 3 | 15,876 | 5,211 | 0 |
  | 4 | 63,504 | 18,733 | 0 |

- **All k.** Every chain is its repeat-free reduction plus zero pieces. A dominating π exists exactly when the sorted values dominate termwise, and zero padding does not change that. So checking all 63 × 63 pairs of reduced lists settles every k; there are 0 violations.
- **The threshold reduction.** Threshold-count dominance coincides with sorted dominance on every pair. This confirms the lane's threshold reduction, which is the core of the Lean finite check.
- **Non-embeddability.** The ordering 0 < 1 < … < 5 is forced up to reflection. The five comparisons all hold, and their gap coefficients are [1,2,2,2,1] on both sides, so their sum gives 0 < 0.
- Not reproduced: the lane's n = 5 minimality scan. It is a diagnostic only.

### C. Lean (PASS)

- The build, leanchecker and audit details are given above.
- The finite check uses `decide +kernel`, with no native_decide or ofReduceBool.
- The reduction lemmas implement exactly the argument verified in B.
- **Recommended target:** the existing `not_majorizationConjecture` together with `witness`. It is adequate as is.

### D. Prior art (bounded PASS)

- The conjecture has been public since 2019.
- Semantic Scholar lists two citers. "Echeloned Spaces" (Forum Math. Sigma 2025) was read; it covers metrizability, Fraïssé limits and Ramsey properties, and nothing on line embedding. "Towards Ordinal Data Science" is a position paper.
- An extended web search found nothing.
- Residual: the classical unidimensional-scaling and absolute-difference literature was not searched body by body.

### E. Significance (QUALIFIED_PASS)

- **Not a routine corollary of Scott or KLST.** Their theorems say that finite representability needs the full cancellation family and that no bounded-order subfamily suffices. Majorization has unbounded order but a restricted shape: each side tiles a single interval along the enumeration. Its failure therefore needs an explicit example.
- **Expected in spirit, though.** It is analogous to Kraft–Pratt–Seidenberg's 1959 five-atom counterexample to de Finetti's axioms for qualitative probability.
- **What it achieves.** It settles the authors' explicitly open n > 5 question with a 6-point witness, beside the n ≤ 4 sufficiency theorem.
- **Depth.** The witness is computer-found and the certificate is a 5-term linear combination, so the result is modest.
- It is not a wording, domain or endpoint correction, and not a parameter instance.
- Root should weigh the measurement-theory caveat.

## Files

- `review.json`: per-gate verdicts, scope readings, recommended Lean targets, objections and next actions.
- `scripts/`:
  - `limited.py` (resource caps) and `fetch.py` (single-request receipts);
  - `cat_verify.py`, `cat_search.py`, `cat_crosscheck.py`, `cat_trivial.py` (366834);
  - `ord_verify.py` (366371);
  - `lean_replay.sh` (strict replay) and `probe_expected.py` (expected values for the Lean probe).
- `fresh/`: the extracted proof files, my audit and statement files, the oleans, and the infeasibility probe `Probe3.lean`.
- `logs/`: full logs with a `*.receipt.json` for every run, including the deliberately capped runs `cat-search-inrange` (CPU cap) and `probe3` (RSS cap).
- `sources/`: fetched pages with dated URL/status/sha256 receipts. `receipts/web-searches.json` records the five web searches, the denied route and the institutional route not used.
