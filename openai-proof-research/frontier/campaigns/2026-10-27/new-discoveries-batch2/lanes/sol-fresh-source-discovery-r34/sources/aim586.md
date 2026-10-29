# 586. The happy-edge conjecture for convex plane spanning trees

**Area:** Computational geometry and geometric reconfiguration

**Status:** 🔵 OPEN

**Last checked:** 2026-09-24

## Problem statement

Let $`P\subset\mathbb R^2`$ be a finite set in strictly convex position. A plane spanning tree on $`P`$ has vertex set $`P`$, straight edges, and no crossing between the interiors of its edges. A flip removes one edge and inserts another, with the resulting graph again a plane spanning tree. The removed and inserted edges may cross each other.

For any two such trees $`T`$ and $`T'`$, prove or disprove that there is a shortest flip sequence

```math
T=T_0,T_1,\ldots,T_k=T'
```

such that

```math
E(T)\cap E(T')\subseteq E(T_i)\qquad(0\le i\le k).
```

Thus all edges shared by the endpoints of the sequence can be retained simultaneously throughout some optimal reconfiguration.

## Application

Preserving shared edges would reduce the search space for optimal transformations of geometric networks. It would justify decomposing shortest-sequence computations along common edges.

## References

1. O. Aichholzer et al., [Reconfiguration of non-crossing spanning trees](https://doi.org/10.20382/jocg.v15i1a9), *Journal of Computational Geometry* **15**(1) (2024), 224–253, Conjecture 17 and the following convex-case observation.
2. O. Aichholzer, J. Dorfer, P. Kramer, C. Rieck and B. Vogtenhuber, [Structural Properties of Shortest Flip Sequences Between Plane Spanning Trees](https://arxiv.org/abs/2603.05205), arXiv:2603.05205 (2026), Conjecture 1 and conclusions.
3. O. Aichholzer, J. Dorfer and B. Vogtenhuber, [Constrained Flips in Plane Spanning Trees](https://doi.org/10.4230/LIPIcs.GD.2025.5), *GD 2025*, Sections 4–6.

## Status review

Common convex-hull edges can already be preserved. Reference [3] proves the happy-edge property for compatible flips, which forbid crossings between the removed and inserted edges; that result does not resolve shortest sequences under the unrestricted flip operation above. The analogous property for rotations is false. Reference [2] still states the displayed conjecture while disproving the stronger parking and reparking proposals. Searches found no matching resolution or duplicate.
