# MathDB 340121: Positive proportion conjecture for partitions into MSTD subsets

- Problem: https://mathdb.com/p/340121
- Source: Hung Viet Chu, Noah Luntzlara, Steven J. Miller and Lily Shao, “Infinite Families of Partitions into MSTD Subsets”, arXiv:1808.05460 (2019). (https://arxiv.org/abs/1808.05460)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `mathdb_340121`, `mathdb_340121_labelled`, `labelled_positive_proportion`, `conjecture15Count`, `conjecture15`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Significance modest (review 0.35). Journal versions and the classical MSTD papers were not read in full; no proof for k >= 3 was found in a bounded search, and the ProbXiv record is open.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. For every fixed k >= 2 there are c > 0 and R such that for all r >= R, at least a proportion c of the partitions of {1, ..., r} into k nonempty classes have every class an MSTD set (|A + A| > |A - A|). This settles the positive-proportion conjecture of Chu, Luntzlara, Miller and Shao for all k; the case k = 2 was known. The proof uses a periodic modular colouring of the two ends of the interval together with the fringe method. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

A **$k$-decomposition into MSTD subsets** is a partition of $I_r=\{1,2,\ldots,r\}$ into $k$ subsets, each having more pairwise sums than pairwise differences. **Positive proportion conjecture.** For any finite $k\ge 2$, the proportion of $k$-decompositions of $I_r$ into MSTD subsets is bounded below by a positive constant. This would extend the known positive-constant lower bound for $k=2$ and give a uniform abundance result for decompositions into any fixed finite number of MSTD subsets; the source does not establish the conjecture for general $k$.

## Summary of the result

For every fixed k >= 2 there are a constant c > 0 and a threshold R such that for all r >= R at least a proportion c of the partitions of {1, ..., r} into k nonempty classes have every class an MSTD set (more sums than differences). This proves the positive-proportion conjecture of Chu, Luntzlara, Miller and Shao; the case k = 2 is due to Asada, Manski, Miller and Suh. The new ingredient is a k-colouring of Z/2hZ, h odd, in which antipodal residues get different colours and every colour class has full modular sumset, laid periodically on both ends of the interval.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
