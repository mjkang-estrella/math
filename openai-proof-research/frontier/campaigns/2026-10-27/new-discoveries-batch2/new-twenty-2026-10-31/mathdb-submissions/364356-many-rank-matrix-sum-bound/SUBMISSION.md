# MathDB 364356: The many-rank matrix-sum equidistribution conjecture

- Problem: https://mathdb.com/p/364356
- Source: Nick Gill, Noam Lifshitz, László Pyber and Endre Szabó, “Initiating the proof of the Liebeck–Nikolov–Shalev conjecture”, arXiv:2408.07800 (2024). (https://arxiv.org/abs/2408.07800), Conjecture 5.5
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `MatrixSum.totalRank_sum_bound`, `MatrixSum.manyRanks_equidistribution`, `MatrixSum.manyRanks_explicit`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Modest significance (user may overrule). The conjecture is read as a one-sided O(1) upper bound; the referee showed a two-sided reading is false. Journal versions of the source are unread.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Let k matrices be chosen independently and uniformly from the n by n matrices over the field with q elements of prescribed ranks r_1, ..., r_k. If the ranks sum to at least 2n, the probability that their sum equals any fixed matrix is at most 32768 q^(-n^2), uniformly in q, n, k and the ranks. For ranks at least epsilon n and k at least ceil(2/epsilon) this gives the many-rank equidistribution conjecture (Conjecture 5.5) of Gill, Lifshitz, Pyber and Szabo in its upper-bound form. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $\operatorname{Mat}^{n\times n}_q$ be the additive group of $n\times n$ matrices over $\mathbb F_q$. For integers $r_1,\ldots,r_k,t$ with $0\le r_i,t\le n$, let $\mathcal N^{n\times n}_q(r_1,\ldots,r_k;t)$ denote the number of $k$-tuples of matrices of respective ranks $r_1,\ldots,r_k$ whose sum is a fixed matrix of rank $t$, and let $\mathcal R^{n\times n}_q(r)$ denote the number of matrices of rank $r$. **Many-rank matrix-sum equidistribution conjecture.** For every $\epsilon>0$ there exists $K(\epsilon)$ such that, if $k\ge K(\epsilon)$ and $\epsilon n\le r_1,\ldots,r_k\le n$, then

$$
\mathcal N^{n\times n}_q(r_1,\ldots,r_k;t)=\operatorname{O}(1)\,\frac{\mathcal R^{n\times n}_q(r_1)\cdots\mathcal R^{n\times n}_q(r_k)}{q^{n^2}}.
$$

The source introduces this as the second of two conjectural generalizations of results in the paper; no resolution status is supplied.

## Summary of the result

For n by n matrices over a finite field with q elements: if prescribed ranks r_1, ..., r_k sum to at least 2n, then for every target matrix the number of k-tuples of matrices of those ranks with that sum is at most 32768 q^(-n^2) times the product of the sizes of the rank classes. The constant is uniform in q, n, k and the ranks. With all ranks at least epsilon n and k at least ceil(2/epsilon) this proves Conjecture 5.5 of Gill, Lifshitz, Pyber and Szabo in its upper-bound (O(1)) reading; a two-sided reading is false already over F_2 with n = 1. The source proves the case of three summands of rank at least 2n/3. Significance is modest.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
