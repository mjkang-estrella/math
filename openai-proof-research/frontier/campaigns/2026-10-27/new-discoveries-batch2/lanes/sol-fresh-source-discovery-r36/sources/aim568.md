# 568. Sharp permutation bound for triangular parts of correlation matrices

**Area:** Numerical linear algebra and iterative methods

**Status:** 🔵 OPEN

**Last checked:** 2026-09-24

## Problem statement

For an integer $`n\ge1`$, let $`B\in\mathbb C^{n\times n}`$ be Hermitian positive semidefinite with $`B_{ii}=1`$ for every $`i`$. For a permutation $`\sigma`$ of $`\{1,\ldots,n\}`$, let $`P_\sigma`$ be its permutation matrix and let $`L_\sigma`$ denote the strictly lower triangular part of $`P_\sigma BP_\sigma^*`$.

Prove or disprove Oswald's conjecture that every such $`B`$ admits a permutation satisfying

```math
\|L_\sigma\|_2\le\frac{2}{\pi}\|B\|_2,
```

where $`\|\cdot\|_2`$ is the spectral norm.

Equivalently, determine whether

```math
\sup_{n\ge1}\ \sup_{\substack{B=B^*\succeq0\\B_{ii}=1}}\ \min_\sigma\frac{\|L_\sigma\|_2}{\|B\|_2}=\frac2\pi.
```

The proposed constant is uniform in dimension. The all-ones matrices show that no smaller universal constant can work: permutations leave them unchanged and their strictly lower triangular parts have norm asymptotic to $`2n/\pi`$, while the full matrices have norm $`n`$.

## Application

The norm of the triangular part enters convergence bounds for successive over-relaxation after reordering the equations. A sharp estimate would quantify how much a suitable single permutation can improve these bounds independently of the system size.

## References

1. P. Oswald and W. Zhou, [Correction: Random reordering in SOR-type methods](https://doi.org/10.1007/s00211-023-01365-9), *Numerische Mathematik* **154** (2023), 521–525. Section 1, equation (2) and the conjecture on page 522.
2. P. Oswald and W. Zhou, [Random reordering in SOR-type methods](https://doi.org/10.1007/s00211-016-0829-7), *Numerische Mathematik* **135** (2017), 1207–1220. Read together with [1].

## Status review

The correction proves a dimension-independent bound with constant $`122.3`$ for positive semidefinite matrices. It withdraws the earlier claimed constant $`32.42`$ and explicitly proposes $`2/\pi`$ for the unit-diagonal class. Its estimates for the expectation of a squared triangular-part matrix do not imply the sharp bound for an individual permutation.

No matching resolution or announcement was found in the current literature, arXiv-indexed, author-page, GitHub and native Palomar checks. Native Zenodo access returned HTTP 403; indexed searches found no matching announcement. The exact searches and duplicate audit are recorded in the accompanying numerical-journal review.
