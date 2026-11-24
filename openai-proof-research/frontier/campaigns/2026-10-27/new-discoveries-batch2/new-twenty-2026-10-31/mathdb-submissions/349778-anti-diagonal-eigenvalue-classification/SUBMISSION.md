# MathDB 349778: Strong anti-diagonal eigenvalue property conjecture for stochastic matrices

- Problem: https://mathdb.com/p/349778
- Source: John R. Britnell and Mark Wildon, Linear Algebra and its Applications 641 (2022), arXiv:2102.08469, Conjecture 2.6. (https://arxiv.org/abs/2102.08469)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Classification349778.mathdb349778`, `Classification349778.mathdb349778_all`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Bounded literature search only. The proof is about one page built on the source's own Lemma 2.2 and Proposition 2.3, and its maximum-principle idea is natural, so a specialist could call it a neat short proof of a conjecture the authors verified only for n <= 4 (cross-model confidence: not routine 0.65, not public 0.85). One reading choice: 'distinct eigenvalues' is applied to the matrix L itself, which the source's sentence before the conjecture supports; a probe of 1,474 structured cases found no counterexample under the other reading either. Closest unpublished related work: Ochiai, Sasada, Shirai and Tsuboi, arXiv:1403.6797.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. A stochastic matrix with distinct eigenvalues has the global anti-diagonal eigenvalue property if and only if it is a binomial transform B Diag(a) B^{-1}. This is Conjecture 2.6 of Britnell and Wildon (arXiv:2102.08469), which the source proves for n <= 4 and away from an exceptional set. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $A$ be a stochastic matrix with distinct eigenvalues. Say that $A$ has the **strong anti-diagonal eigenvalue property** when it satisfies the stronger anti-diagonal eigenvalue condition defined in the paper, and let $H^\lambda$ denote the parameterized family of lower-triangular matrices introduced there. **Strong anti-diagonal eigenvalue property conjecture.** $A$ has the strong anti-diagonal eigenvalue property if and only if it is of the form $H^\lambda$. The conjecture would classify stochastic matrices with distinct eigenvalues satisfying this strengthened spectral property; the paper states that it can be proved for $n\leqslant4$, while the general case is left open.

## Summary of the result

For every n and every row-stochastic n x n matrix A with n distinct eigenvalues, A has the global anti-diagonal eigenvalue property (every leading block is lower triangular and real diagonalizable, and the eigenvalues of the block times the reversal matrix are the signed diagonal entries with multiplicity) if and only if A is a binomial transform B Diag(a) B^{-1} of some vector a. This is Conjecture 2.6 of Britnell and Wildon. The source proves the easy direction, the converse away from an exceptional algebraic set, and the cases n <= 4. The proof here is by induction on the size: a maximum principle for iterated finite differences of the eigenvectors forces them into a polynomial flag when the last parameter is positive, and a determinant identity excludes the remaining zero case because it would repeat an eigenvalue. Lean states the property block by block as the conjecture does, not through the eigenbasis property of the source's Theorem 2.9, and assumes no moment representation.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
