# MathDB 348549: Bruhn–Rautenbach's Fano-plane determinant conjecture

- Problem: https://mathdb.com/p/348549
- Source: Igor Araujo, József Balogh and Yuzhou Wang, “Maximum determinant and permanent of sparse 0-1 matrices”, arXiv:2011.01892 (2020), Section 6; Linear Algebra Appl. 645 (2022) 194–228. The conjecture goes back to Bruhn and Rautenbach, “Maximal determinants of combinatorial matrices”, arXiv:1711.09935, Linear Algebra Appl. (2018). https://arxiv.org/abs/2011.01892
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `SparseDet.mathdb_348549`, `SparseDet.mathdb_348549_integer`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The journal texts (LAA 2018 and 2022) were not read in full (publisher and NSF copies refused or failed); the indexed journal passages still state the conjecture, and every later paper found calls it open. Cross-model confidence 0.9, not routine 0.85. No second cross-model lane read the finished Lean: root compared the final theorem and every definition with the endpoint the Claude Opus reviewer had written (identical), and the GPT-6.1 Sol final check compared the statement with both source papers and reran the scalar inequalities, the Fano case and an exhaustive check for n ≤ 5.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Bruhn and Rautenbach's conjecture (as stated by Araujo, Balogh and Wang, arXiv:2011.01892): every n×n 0-1 matrix with at most 3n ones has determinant at most 24^(n/7), with equality for disjoint copies of the Fano plane's incidence matrix. The best published bounds were 2^(2n/3) and 24^(n/6). The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $A\in\{0,1\}^{n\times n}$ have at most $3n$ non-zero entries. **Bruhn–Rautenbach's conjecture.** The determinant of $A$ is at most $24^{n/7}$. The bound is motivated by the incidence matrix of the Fano plane, whose determinant is $24$, and by disjoint unions of such matrices.

## Summary of the result

Every n×n 0-1 matrix with at most 3n ones satisfies |det A|^7 ≤ 24^n, so det A ≤ 24^(n/7), with equality for disjoint unions of Fano incidence matrices. The best published bounds were 2^(2n/3) (Araujo, Balogh and Wang) and 24^(n/6) (Scheinerman). The proof normalizes the matrix on both sides by its row and column degrees, bounds the logarithm of the determinant of the normalized Gram matrix through its trace and the trace of its square with degree-dependent centres (an integer-degree envelope that is sharp exactly at degree three), and closes with a linear edge/vertex potential that survives deletion of rows and columns of degree one; the induction runs on the potential bound, which needs no density hypothesis, so a deletion that raises the density is harmless. Lean proves the integer form |det A|^7 ≤ 24^n and derives the printed real-power form, and checks that the Fano matrix (21 ones, determinant 24) attains equality and that the hypotheses are satisfiable for every n.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
