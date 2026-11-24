# MathDB 355513: The h*-polynomial of the stable set polytope of the complement of a cycle (Davis–Kohl Conjecture 3.15)

- Problem: https://mathdb.com/p/355513
- Source: Robert Davis and Florian Kohl, “Perfectly Matchable Set Polynomials and h^*-polynomials for Stable Set Polytopes of Complements of Graphs”, arXiv:2207.14759 (2022); Discrete Math. 347(7) (2024) 114018; Conjecture 3.15. https://arxiv.org/abs/2207.14759
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `AntiHole.davis_kohl_conjecture_3_15`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The new contribution is odd n ≥ 5; even n is Davis and Kohl's Corollary 3.14 (the Lean proof covers both parities independently). The journal version (Discrete Math. 347(7) (2024) 114018, doi 10.1016/j.disc.2024.114018) could not be read: the reviewer's probability that it already proves the odd case is 0.10, so its Section 3.1 should be checked by hand before any unqualified novelty claim. The facet description of the antihole stable set polytope is Padberg's classical theorem, used in the paper; the Lean statement is about the lattice points of the dilates of the polytope given by those inequalities. Proof, first (same-model) review and Lean are by Claude Opus 5.5; the cross-model review and final check are by GPT-6.2 Sol (two rounds; not routine 0.65).
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Davis and Kohl (arXiv:2207.14759, Conjecture 3.15) conjectured a formula for the normalized h*-polynomial of the stable set polytope of the complement of the cycle C_n: the perfectly matchable set polynomial of C_n, plus z^{(n+1)/2} when n is odd. They proved even n; the formula is proved here for every n ≥ 4, the new case being odd n, by a direct lattice-point count from the antihole facets with a transfer-matrix argument. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $C_n$ be the cycle graph on $n$ vertices, let $p(C_n;z)$ denote its perfectly matchable set polynomial, and let $\overline{h}^*(C_n;z)$ denote the normalized $h^*$-polynomial of the stable set polytope of the complement of $C_n$. **Cycle polynomial conjecture.** For all $n\geq 4$, 

$$
\overline{h}^*(C_n; z) = p(C_n; z) + \frac{1+(-1)^{n+1}}{2}z^{(n+1)/2}.
$$

The formula agrees with the explicitly computed even-cycle case and with the listed examples through $n=9$; the asserted general identity, particularly for odd cycles, remains open in the source.

## Summary of the result

The conjecture holds for every n ≥ 4. The even case is Davis and Kohl's own Corollary 3.14; the new case is odd n ≥ 5, where the stable set polytope of the complement of the odd cycle is not a lattice-point-friendly compressed polytope and has the extra rank facet. The proof counts the lattice points of the dilates directly from the known facet description of the antihole (Padberg): a greedy recursion around the cycle has a unique real cyclic fixed point; expanding the integer residual weights counts matchings of the cycle, which gives the perfectly matchable set polynomial, and the half-integral fixed points give the one extra monomial z^{(n+1)/2}; a rank-2 transfer matrix assembles the generating function. Lean proves the identity for all n ≥ 4, odd and even, from the lattice-point description of the dilated polytope, so it does not depend on the source's Corollary 3.14, and checks the source's Table 2 for n = 4..7.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
