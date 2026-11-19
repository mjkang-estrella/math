# MathDB 381408: The Catalan triangle Laurent polynomial and positivity conjecture

- Problem: https://mathdb.com/p/381408
- Source: Victor J. W. Guo and Xiuguo Lian, “Proofs of two conjectures on Catalan triangle numbers”, arXiv:1806.02685 (2018). (https://arxiv.org/abs/1806.02685), Conjecture 6.1
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Catalan.mathdb381408`, `Catalan.mathdb381408_laurent`, `Catalan.mathdb381408_nonnegative`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. MathDB 339461 is a duplicate record; submit once and reference both. The full text of Li and Wang (2026) on q-Narayana divisibility is unread (publisher blocks automated access); its abstract concerns a different conjecture. The sharpness of the range is proved on paper only.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. The Guo-Lian q-Catalan-triangle expression, a quotient built from Gaussian binomial coefficients with weights [2k][k]^(2r) q^(j k^2 - (r+1) k), is a Laurent polynomial in q with integer coefficients for every integer j, and has nonnegative coefficients for 0 <= j <= m. This is Conjecture 6.1 of Guo and Lian (also recorded as MathDB 339461). The proof uses a nonnegative Newton-type basis and interpolation at the roots of the denominator; the range for nonnegativity is sharp. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $n_1,\ldots,n_m,n_{m+1}=n_1$ be positive integers. For an integer $j$ and non-negative integers $a,r$ with $a\leqslant n_1$, consider

$$
\frac{1}{[n_m+a]}{n_1+n_m\brack n_1-a}^{-1}\sum_{k=a}^{n_1}[2k][k]^{2r}q^{jk^2-(r+1)k}\prod_{i=1}^{m}{n_i+n_{i+1}\brack n_i+k}.
$$

**Catalan triangle Laurent polynomial and positivity conjecture.** This expression is a Laurent polynomial in $q$, and it has non-negative integer coefficients when $0\leqslant j\leqslant m$. This is presented as a stronger version of Theorem and as a generalization of a conjecture attributed to Guo and Wang; the supplied span does not state whether it has since been resolved.

## Summary of the result

For positive integers n_1, ..., n_m with n_{m+1} = n_1, an integer j, and nonnegative integers a, r with a <= n_1, the Guo-Lian q-Catalan-triangle expression (a quotient of a sum of products of Gaussian binomial coefficients, weighted by [2k][k]^(2r) q^(j k^2 - (r+1) k)) is a Laurent polynomial in q with integer coefficients for every integer j, and all its coefficients are nonnegative for 0 <= j <= m. This is Conjecture 6.1 of Guo and Lian, who proved integrality for 0 <= j <= m. The proof introduces a nonnegative Newton-type basis in which the signed recurrence acts positively, and uses interpolation at the roots of the denominator. The range 0 <= j <= m for nonnegativity is sharp (written proof only). MathDB 339461 is a duplicate record of the same conjecture and is credited once.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
