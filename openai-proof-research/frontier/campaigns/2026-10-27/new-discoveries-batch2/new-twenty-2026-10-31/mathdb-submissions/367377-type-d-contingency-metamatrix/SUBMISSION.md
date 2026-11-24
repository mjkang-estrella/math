# MathDB 367377: Kapranov–Schechtman's total-positivity conjecture for finite Coxeter groups

- Problem: https://mathdb.com/p/367377
- Source: Zhentao Wang, Jiawen Xie and Xuhang Zhang, “On the Total Positivity of Contingency Metamatrices”, arXiv:2503.02213 (2025), Conjecture 1.0.1. https://arxiv.org/abs/2503.02213
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `TypeD.not_totallyPositive_M27`, `TypeD.negativeMinor27`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. One cited bridge: Lean proves the statement for the concrete pair (even signed permutations of 27 coordinates, 27 standard reflections) and proves the generators are distinct involutions that generate the group; that this pair is the Coxeter system of type D_27 is the textbook theorem (Bourbaki VI §4.8, Björner–Brenti §8.2), not formalized (the final check verified the analogous pairs for n = 2..5 by computer). The source does not define total positivity; the strict sense used is Kapranov–Schechtman's (Etingof's appendix), and the negative minor also refutes total nonnegativity. Borderline significance: once one decides to compute type D in closed form the method (Stembridge's fixed-face data plus Burnside) is standard; cross-model reviewer not routine 0.55, final checker 0.55–0.60. That rank 27 is the first failure is not formalized and not claimed. The Lean was started by a GPT-6.1 Sol lane and finished by a Claude Opus 5.5 lane (3,942 lines in 39 modules); because GPT-6.1 Sol hit its usage limit, the final check was by a separate Claude Opus 5.5 lane, the same model family as the packager (the cross-model review is the Opus pre-Lean review of a Sol proof).
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted. Wang, Xie and Zhang (arXiv:2503.02213, Conjecture 1.0.1) conjectured, after Kapranov and Schechtman, that the double-coset metamatrix of every finite Coxeter group is totally positive. For type D_27 a 16×16 minor (rows 0–15, columns 12–27) is negative; ranks 2–26 are totally positive, so the first failure is at rank 27. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $(W,S)$ be a finite Coxeter group of rank $|S|=n$. For subsets $I,J\subset S$, let $W_I$ and $W_J$ be the parabolic subgroups of $W$ of types $I$ and $J$, respectively. Define the metamatrix $M(W)=(M_{pq})_{0\leq p,q\leq n}$ by $$M_{pq}=\sum_{I,J\subset S,|I|=p,|J|=q}|W_I\backslash W/W_J|.$$ **Kapranov–Schechtman's conjecture.** The metamatrix $M(W)$ is totally positive.

## Summary of the result

The conjecture fails for the Coxeter group of type D_27: the 16×16 submatrix of M(D_27) with rows p = 0..15 and columns q = 12..27 has negative determinant (a 372-digit integer), so M(D_27) is not totally positive, not even totally nonnegative. The source proves the conjecture for type B and the exceptional types and does no type-D computation; every rank from 2 to 26 is totally positive (reproduced independently by two lanes, not formalized and not claimed), so no small-rank check finds the failure. The proof identifies parabolic subgroups with stabilizers of face vectors, counts double cosets by Burnside's lemma through fixed-face counts with a type-D gluing identity (Stembridge's fixed-face data are the closest prior work), and turns the result into an explicit integer formula for every entry. Lean works with the concrete group of even signed permutations of 27 coordinates and its 27 standard reflections (the D_27 fork), defines parabolics as generated subgroups and entries as Nat.card of Mathlib's double-coset quotient, proves the formula, evaluates all 256 entries of the minor in the kernel (decide +kernel, no native_decide), and certifies the sign of the determinant by an integer triangular factorization.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
