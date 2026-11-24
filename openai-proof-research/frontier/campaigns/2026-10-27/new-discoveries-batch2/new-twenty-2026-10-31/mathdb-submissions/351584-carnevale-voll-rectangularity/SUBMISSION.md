# MathDB 351584: Carnevale–Voll's factorisation conjecture for multiset Euler–Mahonian polynomials

- Problem: https://mathdb.com/p/351584
- Source: Angela Carnevale and Elena Tielker, “On Denert's statistic”, arXiv:2108.04700 (2021). https://arxiv.org/abs/2108.04700
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Carnevale.source_conjecture_351584`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The Lean theorem is conditional on one named hypothesis, the source's published formula (eq. (10) with Theorems 3 and 10); it must not be described as fully formalized. In the source that formula is a remark justified by citing MacMahon's formula and Theorem 10, not a numbered theorem with its own proof; two reviewers confirmed it by brute force from the literal definitions for all compositions of size up to 7 (one up to 8), and the packet kernel-checks it only for the one-part compositions [1] and [2]. 'Unitary factor' means a nonconstant factor, as in the source (the MathDB record's wording omits 'nonconstant'). The record 333538 (Carnevale and Voll's original Conjecture B) is the same conjecture and is resolved by the same theorem through Han's equidistribution, a step not in Lean: one result, not two. Bounded literature search only; closest later work: Ayyer and Sundaravaradan, arXiv:2606.12919 (rectangular reciprocity, no exclusion of non-rectangles). Cross-model confidence: correct 0.95, not routine 0.75, Lean statement equals the printed conjecture modulo the formula 0.97.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved, kernel-checked modulo one published formula. The (den, exc) polynomial of the multiset permutations S_eta has a unitary factor if and only if eta = (m^r) with r even and m odd, and then it is (1 + x^{rm/2} y) times a polynomial with no unitary factor. This is Conjecture 23 of Carnevale and Tielker (the (den, exc) form of Carnevale and Voll's Conjecture B). The Lean proof takes the source's generating-function formula (eq. (10), from MacMahon and Han) as a named hypothesis. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $\eta$ be a composition, and let $S_{\eta}$ denote the associated multiset permutations. For a polynomial $f\in\mathbb{Z}[x,y]$, call it **unitary** if there are $F\in\mathbb{Z}[Y]$ and $a,b\in\mathbb{N}_0$ such that $f(x,y)=F(x^ay^b)$ and every complex root of $F$ has absolute value $1$.

**Carnevale–Voll's factorisation conjecture.** The polynomial giving the joint distribution of $(\operatorname{den},\operatorname{exc})$ over $S_{\eta}$ has a unitary factor if and only if $\eta=(m^r)$ is a rectangle with $r$ even and $m$ odd. In that case,

$$
\sum_{w\in S_{\eta}}x^{\operatorname{den}(w)}y^{\operatorname{exc}(w)}=\left(1+x^{\frac{rm}{2}}y\right)f^{\eta}_0(x,y),
$$

where $f^{\eta}_0(x,y)$ has no unitary factor.

This is a reformulation of the factorisation conjecture for joint $(\operatorname{des},\operatorname{maj})$ distributions over multiset permutations. The stated factorisation singles out the unitary factor $1+x^{rm/2}y$ in exactly the even-by-odd rectangular cases; its resolution is not given in the supplied text.

## Summary of the result

For every composition eta, the polynomial giving the joint distribution of Denert's statistic and excedances over the multiset permutations S_eta has a (nonconstant) unitary factor if and only if eta = (m^r) is a rectangle with r even and m odd; in that case the factor is 1 + x^{rm/2} y, it occurs once, and the cofactor has no unitary factor. This is Conjecture 23 of Carnevale and Tielker, the (den, exc) form of Conjecture B of Carnevale and Voll. Lean defines the words, excedances, Denert's statistic, the polynomial and the unitary predicate literally and proves both directions, the printed factor, multiplicity one and the statement about the cofactor, under ONE named hypothesis: the source's published generating-function formula for the polynomial (its equation (10) with Theorems 3 and 10, that is MacMahon's formula transported by Han's equidistribution), which is not formalized. The new mathematics is the exclusion of non-rectangles: a unitary factor forces poles of the generating function at roots of unity whose orders are incompatible, by a strict sine-sum inequality, unless all parts are equal.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
