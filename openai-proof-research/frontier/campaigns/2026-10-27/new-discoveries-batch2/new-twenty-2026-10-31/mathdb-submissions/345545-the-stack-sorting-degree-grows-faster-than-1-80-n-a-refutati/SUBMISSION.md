# MathDB 345545: The stack-sorting degree grows faster than 1.80^n: a refutation of the Defant–Propp interval conjecture

- Problem: https://mathdb.com/p/345545
- Source: Defant-Propp arXiv:2002.07144 Conjecture 4.4; MathDB 345545
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `StackSort.Round6.mathdb_345545 : ¬ Conj (Conj := ∃ L, Tendsto (fun n => deg n ^ (1/n : ℝ)) atTop (𝓝 L) ∧ L ∈ Ioo 1.68 1.73, deg n = P n / n!, P n the literal fibre-pair count of West's stack-sorting map); limit_ge : every such limit is ≥ 1.73; nonvacuity : ∃ᶠ n, 1.73 < deg n ^ (1/n); subsequence_companion; plus mathdb_345545_max and max_companion for the MathDB maximum-fibre paraphrase (no credit)`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `stacksort-source6.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: Google Scholar, MathSciNet and zbMATH not consulted; OpenAlex cited-by coverage bounded trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; the bound 1.80468, P_21..P_82 and the estimate 1.95 are ordinary exact computations, not kernel-checked; limit existence (source Theorem 2.5) not formalised; the formal statements cover every possible limit and frequent exceedance; direct literal kernel reductions of P_5 and P_6 exceeded the caps (both are proved through exactSeeds20_proved) not_claimed: Credit for the maximum-fibre paraphrase; That the new recursion is essential for the bare refutation; The exact value of the limit; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Defant-Propp interval conjecture that the growth rate of the stack-sorting degree lies between 1.68 and 1.73. Every possible limit is at least 1.73 by the formal argument, and exact values through n = 82 give at least 1.80468, with the numerical value about 1.95; the growth is thus faster than the conjectured window. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Defant and Propp, arXiv:2002.07144 v3/v4 Conjecture 4.4 (Electron. J. Combin. 27(3) (2020) P3.51, Conjecture 23), restated as open by Defant (Adv. Math. 2022): the limit lies in (1.68, 1.73). False: every limit is at least 1.73 (Lean), and the exact values through n = 82 give at least 1.80468 (ordinary exact computation); the numerical value is about 1.95.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in stacksort-source6.zip.
