# 503. Exact diameter of the leaf-slide graph on labelled trees

**Area:** Applied topology and network reconfiguration

**Status:** 🔵 OPEN

**Last checked:** 2026-09-23

## Problem statement

Let $`G_n`$ have as vertices all trees with labelled vertex set $`[n]=\{1,\ldots,n\}`$. Two trees are adjacent when one can be obtained from the other by a single *leaf slide*: choose a leaf $`v`$ with neighbor $`w`$, choose a neighbor $`u\ne v`$ of $`w`$ in the current tree, delete $`\{v,w\}`$ and insert $`\{v,u\}`$.

The graph $`G_n`$ is connected. Its distance is the minimum number of these individual slides needed to transform one labelled tree into another. Is

```math
\mathop{\mathrm{diam}}\nolimits(G_n)=\left\lfloor\frac{n^2}{2}\right\rfloor-n
```

for every integer $`n\ge6`$?

The permitted move follows one existing edge adjacent to the leaf's attachment point. Labels are fixed, and each slide has unit cost.

## Application

A tree models a communication network without redundant links. The diameter measures the largest number of local leaf rewiring operations needed between two configurations, giving a worst-case reconfiguration cost under this move rule.

## References

1. D. N. Kozlov, [Network realignment complexes](https://doi.org/10.1007/s41468-025-00204-0), Journal of Applied and Computational Topology **9** (2025), article 8. Definitions 2.1 and 2.3, Proposition 2.4 and Open Question 2.5.
2. F. Klatt, I. Papadopoulos and M. Raffelsiefen, [Network Realignment Complexes over General Graphs](https://arxiv.org/abs/2607.07404), 2026 preprint, §3, Theorem 3.3 and the paragraph following it.

## Status review

The selected journal asks for the exact diameter. Reference [2] proves the displayed expression is an upper bound and conjectures its sharpness for $`n\ge6`$. Its lower bounds are $`\lfloor(3n^2-4n)/8\rfloor`$ for even $`n`$ and $`\lfloor(3n^2-6n)/8\rfloor`$ for odd $`n`$. The authors report exact computations for $`6\le n\le9`$; those computations have not been independently reproduced here.

The universal sharpness statement remains the target. Searches on 23 September 2026, including indexed arXiv, Zenodo, GitHub and Palomar checks, located no matching solution or announcement.
