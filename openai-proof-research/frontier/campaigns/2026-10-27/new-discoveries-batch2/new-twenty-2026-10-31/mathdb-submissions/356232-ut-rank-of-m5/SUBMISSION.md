# MathDB 356232: The monoid M5 = Mon<a,b | aba = ba> has UT-rank exactly 4 over the integer max-plus semiring

- Problem: https://mathdb.com/p/356232
- Source: Carl-Fredrik Nyberg-Brodda, “Tropical one-relation monoids”, arXiv:2209.12612 (2022), Conjecture 2.11. https://arxiv.org/abs/2209.12612
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `M5UT.mathdb356232`, `M5UT.conjecture_2_11`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The statement is for integer max-plus upper triangular matrices and multiplicative (semigroup) embeddings; over the real max-plus semiring a faithful UT_3 representation exists (found by the first review; on paper, outside Lean), and the dual statement for M_8 is an ordinary corollary outside Lean. The UT_4 embedding is Nyberg-Brodda's with the printed entry B₁₁ corrected from 1 to −1; J. D. Mitchell's 2022 public notebook had already flagged that the printed product does not check. Proof, first (same-model) review and Lean are by Claude Opus 5.5; the cross-model review and final check are by GPT-6.2 Sol, which put not-routine at 0.57, just above the floor root uses for counting (0.55). The source is a single arXiv version; no citing work resolves the question.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Nyberg-Brodda (arXiv:2209.12612, Conjecture 2.11) conjectured that the one-relation monoid M5 = Mon<a,b | aba = ba> has UT-rank exactly 4 over the integer max-plus semiring. A counting argument on normal forms shows that no faithful representation by 3×3 upper triangular integer max-plus matrices exists; the 4×4 embedding is the author's, with one printed matrix entry corrected. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $M_5 = \operatorname{Mon}\langle a,b\mid aba=ba\rangle$ be the one-relation monoid with defining relation $aba=ba$. Its **UT-rank** is the least $n$ such that $M_5$ admits a faithful representation into $\operatorname{UT}_n(\overline{\mathbb{Z}})$. **UT-rank conjecture for $M_5$.** The monoid $M_5$ has UT-rank exactly $4$. This is the remaining question for the UT-tropical embeddings considered here: an embedding into $\operatorname{UT}_4(\overline{\mathbb{Z}})$ is known, but it is not known whether smaller matrices suffice.

## Summary of the result

The conjecture holds: M5 embeds in the upper triangular 4×4 matrices over the max-plus semiring on ℤ ∪ {−∞}, and in no smaller size. The new part is the lower bound. Fix the sum of the first and last exponents of a normal form C^α A^β B^γ; the defining relation then forces every entry of the image except the (1,3) entry to be determined, while that one entry can take only linearly many integer values; there are quadratically many normal forms, so two of them collide and no homomorphism into UT_3 is injective (sizes 1 and 2 are handled the same way). The argument uses that the entries are integers: over the real max-plus semiring a faithful UT_3 representation exists, so the statement is specific to ℤ. The upper bound is the source's Lemma 2.9 with one printed entry corrected (B₁₁ = −1); Lean also proves that the matrix as printed (B₁₁ = 1) is not injective. Lean states the conjecture with M5 as a presented monoid, UT_n as the subsemigroup of upper triangular matrices over MinTropical (WithTop ℤᵒᵈ) (proved to be max-plus on ℤ ∪ {−∞}), and an embedding as an injective semigroup homomorphism.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
