# MathDB 331690: The achromatic number bound by the harmonic index

- Problem: https://mathdb.com/p/331690
- Source: Baoyindureng Wu and Clive Elphick, “Upper bounds for the achromatic and coloring numbers of a graph”, arXiv:1511.00537 (2015). (https://arxiv.org/abs/1511.00537)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `fin_complete_colouring_le_two_randicPrime`, `fin_achromatic_le_two_randicPrime`, `fin_truth_set`, `wuElphickConjecture41`, `not_wuElphickConjecture41Literal`, `wuElphickConjecture42`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The literal MathDB statement includes edgeless graphs, where it fails trivially; credit is for the theorem on graphs with an edge (root judgment; user may overrule). Significance modest (review 0.35). Lin and Wang, Discrete Applied Mathematics 371 (2025) 60-64, was read only in the publisher abstract and excerpts: their main theorem excludes both colouring numbers, but the full text was not accessible.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved for every graph with at least one edge. Let R'(G) be the sum over edges uv of 1/max(d(u), d(v)). Every complete colouring of G, proper or not, uses at most 2R'(G) colours, so the achromatic number satisfies psi(G) <= 2R'(G) (Wu-Elphick Conjecture 4.1), and the same bound holds for the pseudoachromatic and Grundy numbers. As literally stated ("for any graph") the inequality fails exactly for nonempty graphs with no edges, where psi = 1 and R' = 0. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $G$ be a graph. The **achromatic number** $psi(G)$ is the largest number of colors in a complete proper vertex coloring, and $R'(G)$ denotes the inverse degree-based index used in the source. **The achromatic-number conjecture.**

$$
\psi(G)\leq 2R'(G).
$$

The source presents this as a conjecture motivated by the preceding bounds. Its status is not resolved in the supplied text.

## Summary of the result

For every finite simple graph G with at least one edge, every complete colouring (proper or not) uses at most 2R'(G) colours, where R'(G) is the sum over edges uv of 1/max(d(u), d(v)). Hence the achromatic number, the pseudoachromatic number and the Grundy number are all at most 2R'(G), which proves Wu-Elphick Conjecture 4.1 (and 4.2) for all graphs with an edge. The literal statement "for any graph" fails exactly at nonempty edgeless graphs, where the achromatic number is 1 and R' is 0; Lean proves this exact truth set. The source excludes isolated vertices in its neighbouring results, so the result is a proof of the intended conjecture.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
