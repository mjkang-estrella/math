# 617. Polynomial-size convex difference decompositions

**Area:** Polyhedral geometry and optimization

**Status:** 🔵 OPEN

**Last checked:** 2026-09-24

## Problem statement

A continuous piecewise affine function $`f:\mathbb R^d\to\mathbb R`$ has $`q`$ pieces if $`q`$ is the smallest number of full-dimensional cells in a finite polyhedral complex covering $`\mathbb R^d`$ on whose cells $`f`$ is affine. Cells meet along common faces; pieces count regions, not merely distinct affine formulas.

Does a universal polynomial $`p`$ exist such that every such $`f`$ admits

```math
f=g-h,
```

where $`g,h:\mathbb R^d\to\mathbb R`$ are convex continuous piecewise affine functions, each with at most $`p(d,q)`$ pieces? The polynomial and its degree must be independent of $`d`$, $`q`$ and $`f`$.

## Application

Small decompositions would control the cost of difference-of-convex optimization and exact neural-network representations of piecewise affine functions.

## References

1. M.-C. Brandenburg, M. Grillo and C. Hertrich, [Decomposition Polyhedra of Piecewise Linear Functions](https://doi.org/10.1007/s00454-026-00875-1), *Discrete & Computational Geometry* (2026), Section 2.2 and Problem 9.1. [arXiv:2410.04907](https://arxiv.org/abs/2410.04907).

## Status review

The September 2026 article explicitly leaves this uniform polynomial bound open. Existence of some convex difference decomposition is classical. Its polyhedral method optimizes over a fixed compatible complex and does not establish the asserted global size bound. A proposed higher-dimensional extension of the Tran–Wang construction is disproved in the article.
