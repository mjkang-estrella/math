# 564. The sharp radius in quantitative Steinitz selection

**Area:** Convex geometry and sparse approximation

**Status:** 🔵 OPEN

**Last checked:** 2026-09-24

## Problem statement

Does there exist an absolute constant $`c>0`$ such that, for every integer $`d\ge2`$ and every finite set $`Q\subset\mathbb R^d`$ satisfying

```math
B_2^d\subseteq\mathop{\mathrm{conv}}\nolimits(Q),\qquad B_2^d=\{x:\|x\|_2\le1\},
```

there is a subset $`F\subseteq Q`$ with $`|F|\le2d`$ and

```math
\frac{c}{\sqrt d}B_2^d\subseteq\mathop{\mathrm{conv}}\nolimits(F)?
```

The retained ball has the same center, the origin. The constant must be independent of the dimension, the number of input points and their positions.

## Application

This asks how well a large convex hull can retain its size after selecting only twice as many points as the dimension. Such selection bounds support sparse geometric representations and quantitative versions of Helly and Carathéodory theorems.

## References

1. G. Ivanov, [Quantitative Steinitz theorem and polarity](https://doi.org/10.1007/s00454-025-00743-4), *Discrete & Computational Geometry* **75** (2026), 1405–1413, introduction. [arXiv:2403.14761](https://arxiv.org/abs/2403.14761).
2. G. Ivanov and M. Naszódi, [Quantitative Steinitz theorem: a polynomial bound](https://doi.org/10.1112/blms.12965), *Bulletin of the London Mathematical Society* (2024), Theorem 1 and Conjecture 1.1.
3. G. Ivanov, [A colorful Steinitz theorem with different centers](https://arxiv.org/abs/2609.21927), arXiv:2609.21927 (18 September 2026), Proposition 1.2.

## Status review

The proved uniform radius in [2] is $`1/(6d^2)`$. The $`d^{-1/2}`$ target is explicitly conjectured there and retained in [1]. Examples show that its order in the dimension would be sharp up to an absolute constant. The September 2026 paper [3] still uses the $`1/(6d^2)`$ estimate; its new colorful result has different assumptions and does not establish the displayed radius.

This is a point-selection problem, distinct from Steinitz rearrangement and vector-signing bounds. A public numerical algorithm repository implements the known polarity estimate and explicitly describes the sharp order as conjectural. Current checks found no matching resolution.
