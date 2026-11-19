# MathDB 359778: The three-component-intersection extremal conjecture for odd n

- Problem: https://mathdb.com/p/359778
- Source: Imre Leader, Žarko Ranđelović and Ta Sheng Tan, “A Note on Hamiltonian-Intersecting Families of Graphs”, arXiv:2309.00757 (2023). (https://arxiv.org/abs/2309.00757), Conjecture 7
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Theta359778.theta_family`, `Theta359778.lrt_conj7_fails`, `Theta359778.not_conjecture`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The Discrete Mathematics journal version of the source is unread (publisher refuses automated access). The conjecture was restated unchanged in Randelovic 2025 Cambridge thesis.
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the three-component-intersection extremal conjecture for odd n. For every h >= 1, on n = 6h-1 labelled vertices, the graphs missing at most one edge from each of at most two of the three paths of a spanning theta graph form a family of (1+6h+12h^2) 2^(C(n,2)-6h) members whose pairwise intersections have at most three components, beating the conjectured bound ((n+3)^2/8) 2^(C(n,2)-n) by a factor tending to 4/3. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $[n]=\{1,2,\ldots,n\}$ with $n$ odd, and let $\mathcal{F}$ be a family of graphs on $[n]$.

**Three-component-intersection conjecture.** If the intersection of any two graphs in $\mathcal{F}$ has at most three components, then

$$
|\mathcal{F}|\leq \frac{(n+3)^2}{8}\frac{1}{2^n}\cdot 2^{\binom{n}{2}}.
$$

For more than two components, the authors report that fixed-Hamilton-cycle constructions no longer appear optimal. For three components they suspect the bound is attained by a construction based on two half-sized cycles meeting at a point, although the displayed conjecture is the stated quantitative claim.

## Summary of the result

For every h >= 1, on n = 6h-1 labelled vertices there is a family of (1+6h+12h^2)*2^(C(n,2)-6h) graphs whose pairwise intersections all have at most three components, exceeding the conjectured bound ((n+3)^2/8)*2^(C(n,2)-n); the ratio tends to 4/3. The family consists of all graphs missing at most one edge from each of at most two of the three paths of a spanning theta graph. At n = 5 it has 304 graphs against a bound of 256. Lean proves the family for all h, failure above every order threshold, and the literal negation.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
