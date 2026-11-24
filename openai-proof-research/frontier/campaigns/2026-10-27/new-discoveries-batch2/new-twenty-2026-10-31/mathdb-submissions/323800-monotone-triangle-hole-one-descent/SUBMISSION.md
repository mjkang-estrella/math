# MathDB 323800: Riegler's hole-one-descent identity for the monotone-triangle polynomial

- Problem: https://mathdb.com/p/323800
- Source: Lukas Riegler, “Generalized Monotone Triangles: an extended Combinatorial Reciprocity Theorem”, arXiv:1207.4437 (2012), Conjecture 6; also FPSAC 2013 (Conjecture 5) and Riegler's 2014 Vienna dissertation (Conjecture 4.6.5). https://arxiv.org/abs/1207.4437
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `MT.riegler_conjecture6`, `MT.riegler_conjecture6_mt`, `MT.alpha_eq_mtNum`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Lean proves the statement with α defined by Fischer's operator formula; that this α counts monotone triangles at increasing rows is proved in Lean, while two standard identifications are on paper only: polynomiality and uniqueness (so that the operator formula is Riegler's polynomial also at the descent row), and the classical bijection between monotone triangles and alternating sign matrices behind A_{n,j}. The method (operator-formula certificates) is Fischer–Riegler's; the contribution is the specific four-position identity. Riegler's 2014 dissertation still states the conjecture as open (p. 75; read through the text in the catalogue record); one citing thesis (Izanloo 2019) is unread (tangential by its abstract). Proof, first (same-model) review and Lean are by Claude Opus 5.5; the cross-model review and final check are by GPT-6.2 Sol (two rounds; not routine 0.59, close to the floor of 0.55 root uses for counting).
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Riegler (arXiv:1207.4437, Conjecture 6) conjectured that the monotone-triangle polynomial at the row 1, …, i−1, i+1, i, i+1, …, n equals −Σ_j (j − i) A_{n,j}, with A_{n,j} the refined alternating sign matrix numbers, having proved i = 1. The identity is proved for every i by a new four-position relation for the polynomial, certified by Fischer's operator formula, and telescoping from i = 1. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $A_{n,j}$ denote the number of alternating-sign matrices of size $n$ whose unique $1$ in the first row is in column $j$, and let $n\geq1$ and $i=1,\ldots,n-1$. **Hole-one-descent conjecture.** The identity

$$
\alpha(n+1;1,2,\ldots,i-1,i+1,i,i+1,\ldots,n)=-\sum_{j=1}^{n}(j-i)A_{n,j}
$$

should hold. The source proves the case $i=1$ and obtains part of the general decomposition, but explicitly says that the remaining contribution from two structural classes is an open problem.

## Summary of the result

The conjecture holds for all n ≥ 1 and 1 ≤ i ≤ n − 1. Here α(n; k₁, …, kₙ) is the polynomial that counts monotone triangles with bottom row k₁ < … < kₙ, evaluated at a row with one descent. The proof finds a specific identity among four evaluations of α at neighbouring rows (the four-position identity W1) and certifies it with Fischer's operator formula, by the method of Fischer–Riegler's Lemmas 8.1–8.2; it turns each successive difference in i into a value of α at a row with a repeated entry, which equals the total number A_n of alternating sign matrices, and telescoping from Riegler's published case i = 1 gives the formula. Lean defines α by Fischer's operator formula, proves that it counts monotone triangles at strictly increasing rows, and proves the identity over the full printed range, with A_{n,j} given as α at the deletion rows (and, in a second endpoint, as monotone-triangle counts).

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
