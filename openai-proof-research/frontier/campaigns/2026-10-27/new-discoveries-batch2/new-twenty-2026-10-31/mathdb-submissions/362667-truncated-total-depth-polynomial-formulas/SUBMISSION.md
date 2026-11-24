# MathDB 362667: Polynomial formulas for truncated total depth in ordered trees

- Problem: https://mathdb.com/p/362667
- Source: Stoyan Dimitrov, Martin Minchev and Yan Zhuang, “BFS versus DFS for fixed-level targets in ordered trees”, arXiv:2404.05664v1 (2024). (https://arxiv.org/abs/2404.05664v1), Conjecture 7.6
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `DMZ.dmz_conj_7_6`, `DMZ.dmz_conj_7_6_div`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The conjecture appears in arXiv v1 and is absent from v2 (10 July 2026); the journal text (SIAM J. Discrete Math. 40(4) 1913-1945, doi 10.1137/25M1760891) was not read, only its abstract, which matches v2. If the journal text proves the conjecture this result is not new; nothing found suggests that.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. For every l >= 1 the differences totalD(n,2l-1) - totalDTrunc(n,2l-1) and totalD(n,2l) - totalDTrunc(n,2l) have the conjectured form: a polynomial in n of degree 2l-2 with non-negative integer coefficients and leading coefficient 2l-1 (respectively l), times the stated binomial coefficient, divided by the stated rising factorial, for all n >= l. This is Conjecture 7.6 of arXiv:2404.05664v1. The quadratic coefficient of b_3 is 1133 (Table 3 of v1 prints 113). The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $n$ and $\ell$ be integers satisfying $n\geq \ell\geq 1$. Let $\operatorname{totalD}(n,k)$ denote the total quantity studied in the paper, and let $\operatorname{totalDTrunc}(n,k)$ denote its truncated version. For each $\ell$, let $a_{\ell}(n)$ and $b_{\ell}(n)$ be polynomials in $n$. **Polynomial-formula conjecture.** For all $n\geq \ell\geq 1$, \

$$
\operatorname{totalD}(n,2\ell-1)-\operatorname{totalDTrunc}(n,2\ell-1)=\frac{a_{\ell}(n)}{(n+2\ell+2)^{(2\ell-2)}}{2n \choose n-2\ell-1}
\
$$

 and \

$$
\operatorname{totalD}(n,2\ell)-\operatorname{totalDTrunc}(n,2\ell)=\frac{b_{\ell}(n)}{(n+2\ell+4)^{(2\ell-2)}}{2n+1 \choose n-2\ell-2}.
\
$$

 Here $a_{\ell}(n)$ and $b_{\ell}(n)$ have degree $2\ell-2$ and non-negative integer coefficients; the leading coefficient of $a_{\ell}(n)$ is $2\ell-1$, and the leading coefficient of $b_{\ell}(n)$ is $\ell$. The conjecture would provide a simplified expression for $\operatorname{totalDTrunc}(n,\ell)$, but the supplied text gives no resolution.

## Summary of the result

For ordered trees with n edges and the depth-first-search scores totalD and totalDTrunc of Dimitrov, Minchev and Zhuang, for every l >= 1 there are polynomials a_l and b_l of degree 2l-2 with non-negative integer coefficients and leading coefficients 2l-1 and l such that, for all n >= l, totalD(n,2l-1) - totalDTrunc(n,2l-1) = a_l(n) C(2n, n-2l-1) / (n+2l+2)^(2l-2) and totalD(n,2l) - totalDTrunc(n,2l) = b_l(n) C(2n+1, n-2l-2) / (n+2l+4)^(2l-2), with rising factorials in the denominators. This is Conjecture 7.6 of arXiv v1. The proof is a binomial-sum enumeration of the score difference followed by a pairing argument for non-negativity. Lean also confirms that the quadratic coefficient of b_3 is 1133, where Table 3 of v1 prints 113.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
