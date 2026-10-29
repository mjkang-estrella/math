# 611. Counting cospherical tuples in lattice cubes

**Area:** Discrete geometry and lattice-point counting

**Status:** 🔵 OPEN

**Last checked:** 2026-09-24

## Problem statement

For fixed $`d\ge3`$ and $`n\ge1`$, let $`S(n,d)`$ count ordered tuples of $`d+2`$ pairwise distinct points of $`\{1,\ldots,n\}^d`$ that lie on some Euclidean sphere

```math
\{x\in\mathbb R^d:\|x-a\|_2=R\},\qquad a\in\mathbb R^d,\quad R>0.
```

Count a tuple once even if several spheres contain it. Hyperplanes are not counted as spheres.

Is there a constant $`C_d`$, independent of $`n`$, such that

```math
S(n,d)\le C_d n^{d^2+d-1}
```

for all $`n`$?

## Application

Bounding degeneracies in integer grids controls random constructions of large point sets in spherical general position and the incidence structure of lifted point configurations.

## References

1. A. Ghosal, R. Goenka and P. Keevash, [On Subsets of Lattice Cubes Avoiding Affine and Spherical Degeneracies](https://doi.org/10.1007/s00454-026-00853-7), *Discrete & Computational Geometry* (2026), Conjecture 5.1. [arXiv:2509.06935](https://arxiv.org/abs/2509.06935).

## Status review

The source proves the two-dimensional case and leaves higher dimensions open. Its hypergraph formulation and tuple-selection arguments use distinct points; allowing repetitions would introduce a larger trivial contribution. Dong and Xu's large sphere-avoiding grid subsets settle the related existence lower bound, not this count over all tuples.
