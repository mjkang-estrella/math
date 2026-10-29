# 599. Unimodality of Radon partitions for uniform convex samples

**Area:** Stochastic geometry and convexity

**Status:** 🔵 OPEN

**Last checked:** 2026-09-24

## Problem statement

Let $`d\ge2`$, let $`K\subset\mathbb R^d`$ be a compact convex body with nonempty interior, and set $`n=d+2`$. Draw $`X_1,\ldots,X_n`$ independently from normalized Lebesgue measure on $`K`$. Almost surely their Radon partition is unique: it divides the sample into two nonempty sets $`A,B`$ with intersecting convex hulls.

Choose $`A`$ or $`B`$ with equal probability, independently of the sample, and let $`p_k`$ be the probability that the chosen set contains $`k`$ points. Prove or disprove that

```math
p_1\le p_2\le\cdots\le p_{\lfloor n/2\rfloor}.
```

Since $`p_k=p_{n-k}`$, this is unimodality of the whole size distribution.

## Application

The question extends classical random-convex-position problems to higher-dimensional samples. It asks whether balanced affine dependencies are more frequent for uniform data in every convex sampling region.

## References

1. S. H. Chan, G. Kalai, B. Narayanan, N. Ter-Saakov and M. White, [Unimodality for Radon Partitions of Random Vectors](https://doi.org/10.1007/s00454-026-00870-6), *Discrete & Computational Geometry* (2026), Problem 7.1 and the introduction. [arXiv:2507.01353](https://arxiv.org/abs/2507.01353).

## Status review

The source proves even ultra log-concavity for Gaussian samples, but explicitly leaves unimodality for uniform convex-body samples open. Its counterexamples for general non-Gaussian one-dimensional sample-mean sequences concern a different model and do not refute this statement. A stronger log-concavity extension and a central limit theorem are not counted as separate problems here. Current searches found no matching resolution or duplicate.
