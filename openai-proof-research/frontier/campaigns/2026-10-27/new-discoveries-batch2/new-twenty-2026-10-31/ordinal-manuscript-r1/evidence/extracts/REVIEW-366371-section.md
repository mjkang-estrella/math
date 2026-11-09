<!-- LABELLED EXTRACT (366371 only) of frozen file r61-candidates-review-r1/REVIEW.md (sha256 44395e9b068e61ee233bc7c193cc91a5e169a8264176f58edf8491b0eea9d017); 366834 content omitted (root HOLD). -->

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

