# MathDB 352795: The sparsity conjecture for minimally AP-irreducible sign patterns

- Problem: https://mathdb.com/p/352795
- Source: https://mathdb.com/p/352795/the-sparsity-conjecture-for-minimally-ap-irreducible-sign-pa; https://arxiv.org/abs/2112.00442v3
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `APRefutation.witness`, `APRefutation.refutation`, `APRefutation.expanded_refutation`, `Fresh independent expanded unconditional audit`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `PAPER-v1.md`
- Lean source: `ap-minimal-sparsity-accepted-proof-packet-20261115-v1.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Bounded SUBSTANTIAL: joint essentiality in the same sign pattern uses six row/column-critical positives and three directed cuts in two related supports. The positive-component chain violates the actual native Lemma3.10 extra hypothesis. No inspected complete prior specialization or exact public counterpart supplied this construction. Finite verification alone is neither significance nor a routine-specialization objection. not_claimed: worldwide absence of prior proof; clean historical/current process; unread final journal body equality; audit of trusted upstream theorem truth
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the sparsity conjecture for minimally AP-irreducible zero-diagonal sign patterns, Conjecture 5.1 of arXiv:2112.00442. An explicit pattern of order 5 has 9 nonzero entries, exceeding the asserted bound of 2 times 5 minus 2, and deleting any one of its nonzero entries destroys the AP irreducibility; the numerical realizability Conjecture 5.2 is not addressed. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Refutes the universal sparsity assertion for minimally AP-irreducible zero-diagonal sign patterns: an explicit order5 pattern has9 nonzero entries,exceeding2*5-2=8. AP means signed support irreducible,every row and every column positive,and Aplus-transpose(Aminus) irreducible,where Aminus retains negative entries. Every single nonzero-entry deletion fails AP. This concerns arXiv2112.00442v3 Conjecture5.1,not numerical algebraic-positive realizability Conjecture5.2.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER-v1.md. The complete Lean source is in ap-minimal-sparsity-accepted-proof-packet-20261115-v1.zip.
