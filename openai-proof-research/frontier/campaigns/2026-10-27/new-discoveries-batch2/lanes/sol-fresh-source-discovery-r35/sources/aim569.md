# 569. A sharp Galerkin projection bound on nonobtuse triangles

**Area:** Finite element approximation and numerical PDEs

**Status:** 🔵 OPEN

**Last checked:** 2026-09-24

## Problem statement

Let $`T\subset\mathbb R^2`$ be a nondegenerate triangle whose three interior angles are at most $`\pi/2`$. Let $`p\ge0`$ be an integer, and write $`P_p(T)`$ for the polynomials of total degree at most $`p`$. Denote by $`\Pi_p`$ the componentwise $`L^2(T)`$ orthogonal projection onto $`P_p(T;\mathbb R^2)`$.

For $`f\in H^1(T)`$, define $`G_{p+1}f\in P_{p+1}(T)`$ by

```math
\int_T G_{p+1}f=\int_T f,\qquad
\int_T\nabla G_{p+1}f\cdot\nabla q=\int_T\nabla f\cdot\nabla q
\quad(q\in P_{p+1}(T)).
```

Prove or disprove the Carstensen–Gräßle–Tran conjecture

```math
\|\nabla(f-G_{p+1}f)\|_{L^2(T)}
\le\sqrt2\,\|(I-\Pi_p)\nabla f\|_{L^2(T)}
\qquad(f\in H^1(T)).
```

The constant must hold for every polynomial degree and every nonobtuse triangle, without a positive lower bound on its smallest angle.

## Application

This local approximation inequality controls stabilization parameters in hybrid high-order eigensolvers. The explicit constant would strengthen the rigorous basis for accurate lower bounds on Laplace eigenvalues over meshes containing general nonobtuse triangles.

## References

1. C. Carstensen, B. Gräßle and N. T. Tran, [Adaptive hybrid high-order method for guaranteed lower eigenvalue bounds](https://doi.org/10.1007/s00211-024-01407-w), *Numerische Mathematik* **156** (2024), 813–851; [arXiv:2404.01228](https://arxiv.org/abs/2404.01228). Equations (1.3), (1.12), and Conjecture 2.5 on page 822.
2. C. Carstensen, B. Gräßle and E. Pirch, [Comparison of guaranteed lower eigenvalue bounds with three skeletal schemes](https://doi.org/10.1016/j.cma.2024.117477), *Computer Methods in Applied Mechanics and Engineering* **433** (2025), 117477. Section 3.2, equation (3.6) and the following discussion.

## Status review

Degree-independent stability for each fixed triangle is known. The explicit uniform value $`\sqrt2`$ in [1, Conjecture 2.5] remains the target. Numerical experiments suggest that the square of the optimal constant approaches $`2`$ as the degree increases for several nonobtuse families.

The later comparison paper [2, Section 3.2] still calls this bound conjectural and describes its numerical verification. Its use of $`\sqrt2`$ in computational examples does not establish the full nonobtuse-triangle statement.

No matching proof or announcement was found in the current literature, arXiv, public GitHub and native Palomar checks. Native Zenodo access returned HTTP 403; indexed searches found no matching announcement. No equivalent catalogue entry was found.
