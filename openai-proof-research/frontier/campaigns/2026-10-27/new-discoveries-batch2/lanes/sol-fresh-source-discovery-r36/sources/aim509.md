# 509. Wedge-of-spheres structure of path-product matching complexes

**Area:** Applied and computational topology

**Status:** 🔵 OPEN

**Last checked:** 2026-09-24

## Problem statement

Let $`P_n`$ be the path graph with vertex set $`\{1,\ldots,n\}`$ and edges $`\{i,i+1\}`$. Its categorical product with $`P_m`$ is the graph $`G_{n,m}`$ whose vertices are pairs $`(i,j)`$ and whose edges join $`(i,j)`$ to $`(i',j')`$ exactly when

```math
|i-i'|=|j-j'|=1.
```

Thus both coordinates change along an edge; this is the categorical graph product.

The matching complex $`\mathsf M(G)`$ is the finite abstract simplicial complex with vertex set $`E(G)`$ and with a simplex for each set of pairwise vertex-disjoint edges of $`G`$. Write $`|\mathsf M(G)|`$ for its geometric realization.

For every pair of integers $`n,m\ge6`$, must there exist a finite list of nonnegative integers $`d_1,\ldots,d_r`$ such that

```math
|\mathsf M(G_{n,m})|\simeq\bigvee_{a=1}^{r} S^{d_a}?
```

Here $`\simeq`$ denotes homotopy equivalence, the spheres may have different dimensions, and an empty wedge means a point. Prove the assertion for all such pairs, or give a pair for which it fails.

This is the unresolved range of Conjecture 6.2 in [1]. The source states $`n\ge3`$, $`m\ge6`$; symmetry of the factors and its proved results for widths at most five reduce the remaining question to $`n,m\ge6`$.

## Application

Matching complexes encode collections of compatible pairings: edges represent possible pairings, and a simplex represents a collection that uses no vertex twice. Their topology describes this compatibility structure beyond the size of a largest matching. A wedge decomposition would give a particularly simple homotopy model for these structured grid graphs and, in particular, force their integral homology to be torsion-free. The application is to computational topology of discrete compatibility complexes.

## References

1. R. K. Gupta, S. Sarkar, S. S. Sawant and S. Shukla, [On the matching complexes of the categorical product of path graphs](https://doi.org/10.1007/s41468-026-00238-y), Journal of Applied and Computational Topology **10**, article 19 (2026). Conjecture 6.2, p.43; definitions and Theorem 1.3 on pp.1–5. [arXiv:2403.15298v2](https://arxiv.org/abs/2403.15298v2).

## Status review

Reference [1] proves the wedge-of-spheres property for $`n\ge2`$ and $`3\le m\le5`$ and recalls the known width-two case. Its April 2026 arXiv revision and July 2026 published article both retain Conjecture 6.2. The entry asks for homotopy equivalence, which is stronger than merely computing Betti numbers or excluding torsion.

Searches on 24 September 2026 covered the exact paper and conjecture, later proofs and counterexamples, author publication lists, and indexed arXiv, Zenodo, GitHub and Palomar results. No matching solution or announced solution was located. The [planar Rips-complex question](498-planar-rips-wedges-of-spheres.md) concerns a different family of complexes.
