# 598. Log-concavity of Gaussian convex-hull intersection probabilities

**Area:** Stochastic geometry and convexity

**Status:** 🔵 OPEN

**Last checked:** 2026-09-24

## Problem statement

For integers $`d\ge1`$ and $`n\ge d+3`$, let $`X_1,\ldots,X_n`$ be independent standard Gaussian vectors in $`\mathbb R^d`$. For $`1\le k\le n-1`$, define

```math
q_k(n,d)=\mathbb P\!\left(\mathop{\mathrm{conv}}\nolimits\{X_1,\ldots,X_k\}\cap\mathop{\mathrm{conv}}\nolimits\{X_{k+1},\ldots,X_n\}\ne\varnothing\right).
```

Prove or disprove that this sequence is log-concave:

```math
q_k(n,d)^2\ge q_{k-1}(n,d)q_{k+1}(n,d)\qquad(2\le k\le n-2).
```

By the symmetry $`q_k=q_{n-k}`$, this would also make the intersection probability increase as the two prescribed group sizes become more balanced.

## Application

These probabilities quantify when two random labeled point clouds can be separated by a hyperplane. Log-concavity would give structural control over how linear separability depends on class balance.

## References

1. S. H. Chan, G. Kalai, B. Narayanan, N. Ter-Saakov and M. White, [Unimodality for Radon Partitions of Random Vectors](https://doi.org/10.1007/s00454-026-00870-6), *Discrete & Computational Geometry* (2026), Conjecture 7.2. [arXiv:2507.01353](https://arxiv.org/abs/2507.01353).

## Status review

The source proves the boundary case $`n=d+2`$, using the unique Radon partition of a minimally dependent point set, and explicitly conjectures the extension to larger samples. The displayed quantities concern a prescribed split of labels; they are not the probabilities of the size of a randomly selected part. The September 2026 publication still states the conjecture. Current searches found no matching resolution or duplicate.
