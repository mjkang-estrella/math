# MathDB 362601: The square power partition function inequality conjecture

- Problem: https://mathdb.com/p/362601
- Source: Arindam Roy, “Log-concavity And The Multiplicative Properties of Restricted Partition Functions”, arXiv:2404.03153 (2025). (https://arxiv.org/abs/2404.03153)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoint `Roy362601.restricted_sign_table`; axioms limited to propext, Classical.choice, Quot.sound; independently extracted and replayed from `LEAN-SOURCE-APPENDIX.md`.
- Written proof: `PAPER.md` (independently reviewed, no theorem-affecting gaps).
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Springer final 10.1007/s00026-026-00847-5 unread.
- Produced with AI assistance (GPT-6.2 Sol and Claude Opus 5.5 investigators, independent AI review); not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the exact global sign table for P(a)P(b) against P(a+b), where P(t) counts partitions of t into perfect squares. Writing m and n for the smaller and larger of a and b: equality holds on 33 explicit pairs and the product is smaller on 10 pairs with m >= 4; from m >= 8 the product is strictly greater for every pair, settling the source's conjectured table in both directions. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $p^k(n)$ denote the number of partitions of $n$ into perfect $k$-th powers. In particular, $p^2(n)$ is the square power partition function, and let $a,b$ be positive integers.

**Square power partition function inequality conjecture.** The inequality

$$
p^2(a)p^2(b)\geq p^2(a+b)
$$

has equality and failure exactly in the instances listed in the source's table: equality for $a=1$, $b=1,2,4,5,6,9,10,13,14,18,22$; $a=2$, $b=4,5,9,13$; $a=3$, $b=4$; $a=4$, $b=5,6,7$; $a=5$, $b=5,6,8,11,15$; $a=6$, $b=8,10,12,14$; and $a=7$, $b=8,9,12,13,19$, with the listed complementary instances of failure.

The claim refines the eventual multiplicative inequality for restricted partition functions by identifying its exceptional small-index behavior. The source gives no resolution beyond presenting these instances as a conjectural pattern.

## Summary of the result

SUBSTANTIVE_BOUNDED: exact global sign table for p2(a)p2(b) vs p2(a+b) (33 equalities, 10 failures with m>=4, strict success for m>=8); no inspected source proves an effective global cutoff.

The complete proof is in `PAPER.md`; the complete Lean source is in `LEAN-SOURCE-APPENDIX.md`.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
