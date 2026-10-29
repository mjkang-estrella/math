# 587. A sharp differing-edge bound for convex plane-tree flips

**Area:** Computational geometry and geometric reconfiguration

**Status:** 🔵 OPEN

**Last checked:** 2026-09-24

## Problem statement

Let $`P\subset\mathbb R^2`$ be a finite set in strictly convex position, and let $`T,T'`$ be straight-line spanning trees on $`P`$ whose edges do not cross within either tree. A flip deletes one edge and inserts another, leaving a non-crossing spanning tree; the deleted and inserted edges are allowed to cross each other.

Write $`d_{\mathrm{flip}}(T,T')`$ for the minimum number of flips and

```math
\delta(T,T')=|E(T)\setminus E(T')|=\tfrac12|E(T)\mathbin{\triangle}E(T')|.
```

Prove or disprove that every such pair satisfies

```math
d_{\mathrm{flip}}(T,T')\le\frac53\,\delta(T,T').
```

## Application

The bound would control the number of geometric network updates by the actual difference between the initial and target networks, including instances where most edges already agree. The factor would be optimal.

## References

1. N. Bousquet, L. de Meyer, T. Pierron and A. Wesolek, [Reconfiguration of Plane Trees in Convex Geometric Graphs](https://doi.org/10.1007/s00454-025-00785-8), *Discrete & Computational Geometry* **75** (2026), 431–464, Question 5 and Theorem 4.
2. H. B. Bjerkevik, L. Kleist, T. Ueckerdt and B. Vogtenhuber, [Flipping Non-Crossing Spanning Trees](https://arxiv.org/abs/2410.23809), *SODA 2025*, 2313–2325, full-version Section 7.
3. H. B. Bjerkevik, J. Dorfer, L. Kleist, T. Ueckerdt and B. Vogtenhuber, [Flip Distance of Non-Crossing Spanning Trees: NP-Hardness and Improved Bounds](https://doi.org/10.4230/LIPIcs.SoCG.2026.16), *SoCG 2026*, article 16.

## Status review

Reference [1] constructs pairs with $`\delta=3k`$ requiring exactly $`5k`$ flips, so the proposed constant cannot be reduced. Bounds with leading constant $`5/3`$ in the number of vertices do not imply this statement, because many edges may be shared. Reference [2] explicitly identifies removing its extra common-boundary-edge term as an open improvement. The later hardness and diameter results [3] do not provide the required bound in $`\delta`$. Current searches found no matching resolution or duplicate.
