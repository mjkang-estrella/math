# MathDB 341096: Conjectures on successive threshold values for equal-product partitions

- Problem: https://mathdb.com/p/341096
- Source: Byungchul Cha, Adam Claman, Joshua Harrington, Ziyu Liu, Barbara Maldonado, Alexander Miller, Ann Palma, Tony W. H. Wong and Hongkwon V. Yi, An Investigation on Partitions with Equal Products, arXiv:1811.07451 (2018), Conjecture 5.2; Int. J. Number Theory (2019). (https://arxiv.org/abs/1811.07451)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `EqualProduct.conj52a`, `EqualProduct.conj52b`, `EqualProduct.conj52c`, `EqualProduct.sStar_unique`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Bounded literature search only. The general argument is about one page of elementary combinatorics and the rest is a certified finite computation, so a specialist could call the result elementary (cross-model confidence: not routine 0.65; Lean statement equals the printed conjecture 0.97). The journal text (Int. J. Number Theory, 2019) is unread; the zbMATH review says the conjectures are still stated there. The three starting values 9, 7 and 10 are sharp: each identity fails one step below.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. For equal-product partitions, s*_{n-2}(n) = s*_{n-2}(n-1) + 1 for all n >= 9, s*_{n-1}(n) = s*_{n-1}(n-1) + 1 for all n >= 7, and s*_n(n) = s*_n(n-1) + 1 for all n >= 10. This is Conjecture 5.2 (a), (b), (c) of Cha et al. (arXiv:1811.07451), which the source supports by computed tables only. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

For integers $r\geq2$ and $n\geq3$, let $s_r^*(n)$ be the smallest positive integer, if it exists, such that every integer $s\geq s_r^*(n)$ has at least $r$ different $n$-partitions with the same sum and product, without requiring all parts across the partitions to be distinct. **Successive-threshold conjectures.** The following assertions are conjectured:

1. For all integers $n\geq9$, $s_{n-2}^*(n)=s_{n-2}^*(n-1)+1$.
2. For all integers $n\geq7$, $s_{n-1}^*(n)=s_{n-1}^*(n-1)+1$.
3. For all integers $n\geq10$, $s_n^*(n)=s_n^*(n-1)+1$.

These statements are motivated by computational data. The inequalities $s_r^*(n)\leq s_r^*(n-1)+1$ are known from the theorem preceding the conjectures, but equality in the three displayed ranges remains open.

## Summary of the result

All three parts of Conjecture 5.2 of Cha et al. hold: for every n >= 9, s*_{n-2}(n) = s*_{n-2}(n-1) + 1; for every n >= 7, s*_{n-1}(n) = s*_{n-1}(n-1) + 1; for every n >= 10, s*_n(n) = s*_n(n-1) + 1, where s*_r(n) is the least positive integer beyond which every sum has at least r different partitions into n positive parts with a common product. Both thresholds are shown to exist in every case. The proof has three parts: an elementary stability lemma (below twice the number of parts every partition contains a one, so removing a one is a bijection), explicit infinite families of partitions with equal products that settle all large n, and a certified exhaustive computation for the remaining 77 identities with n <= 34, in which 105 non-existence claims are reduced by padding with ones to 14 enumerations. Lean states partitions as multisets of positive integers and the threshold as the least positive permanent-tail bound, exactly as the source does.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
