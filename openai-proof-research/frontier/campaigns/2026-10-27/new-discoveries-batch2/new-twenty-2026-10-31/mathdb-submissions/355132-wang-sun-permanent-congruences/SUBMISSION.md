# MathDB 355132: Congruence conjectures for permanents of shifted difference matrices

- Problem: https://mathdb.com/p/355132
- Source: Han Wang and Zhi-Wei Sun, “Evaluations of some Toeplitz-type determinants”, arXiv:2206.12317 (2023). (https://arxiv.org/abs/2206.12317)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `WangSun.wang_sun_mod_prime`, `WangSun.wang_sun_mod_prime_sq`, `WangSun.wang_sun_source`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Zhi-Wei Sun's 2021 Chinese-language book, cited by the source as motivation (Conjecture 11.23), is unread.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Let B_n be the n by n integer matrix with entries j - k + delta_jk. For every prime p the permanent of B_{p-1} is congruent to 3 modulo p, and for every odd prime p the permanent of B_p is congruent to 1 + 4p modulo p^2. These are the two permanent congruences conjectured by Wang and Sun; the second uses a reflection lifting lemma modulo p^2 and a telescoping factorial sum. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

For a positive integer $n$, let $[j-k+\delta_{jk}]_{1\leqslant j,k\leqslant n}$ denote the $n\times n$ matrix whose $(j,k)$ entry is $j-k+\delta_{jk}$, where $\delta_{jk}$ is the Kronecker delta, and let $\operatorname{per}(M)$ denote the permanent of a matrix $M$. **Congruence conjecture.** For any prime $p$,

$$
\operatorname{per}[j-k+\delta_{jk}]_{1\leqslant j,k\leqslant p-1}\equiv 3\pmod p.
$$

For any odd prime $p$,

$$
\operatorname{per}[j-k+\delta_{jk}]_{1\leqslant j,k\leqslant p}\equiv 1+4p\pmod {p^2}.
$$

These assertions are motivated by the preceding determinant evaluation in the paper; no resolution or external evidence concerning either congruence is supplied here.

## Summary of the result

Let B_n be the n by n integer matrix with entries j - k + delta_jk. For every prime p, per(B_{p-1}) is congruent to 3 modulo p, and for every odd prime p, per(B_p) is congruent to 1 + 4p modulo p^2. These are the two permanent congruences conjectured by Wang and Sun. The modulo p^2 congruence uses a new reflection lifting lemma and a telescoping factorial sum.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
