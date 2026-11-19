# MathDB 372351: Hook-partition formulae for Kadar–Yu Gram determinant polynomials

- Problem: https://mathdb.com/p/372351
- Source: Benjamin Morris and Paul P. Martin, “On semisimplicity criteria and non-semisimple representation theory for the Kadar-Yu algebras”, arXiv:2512.24535 (2025). (https://arxiv.org/abs/2512.24535), Conjecture 3.31.1
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `BrauerHook.printed_ordinary_clauses_negation`, `BrauerHook.height_five_printed_negation`, `BrauerHook.ordinary_normalized`, `BrauerHook.transpose_normalized`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The link between the Lean Gram matrix and the source Gram matrix is by construction, checked by an independent audit with computations from the source definitions (all 14 worked determinants of the source reproduced), not a kernel-checked theorem. Enyang-Goodman and De Visscher-Martin are unread; no new literature search in the final revision. Determinants are normalized up to a nonzero constant, as the source allows.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted as printed, and proved in corrected form. Morris-Martin Conjecture 3.31.1 gives closed formulas for Gram determinants of one-cup standard modules of the Kadar-Yu algebras for the hook (a+1,1) and its transpose. The printed formula fails by a degree count at a = 5 (174 against 166). With the exponent of the loop variable in (3.3.7) corrected to (a+3)(a+2)(a-2)/6 and the missing plus restored in (3.3.10), the formulas hold for the ordinary hook for all a >= 2 and the transposed hook for all a >= 1, for every tail length. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $l$, $l'$, and $l”$ be integer parameters, and let $C^{(\lambda)}(\alpha)$ and $P_n^{(\lambda)}(\alpha)$ denote the factors in the Kadar–Yu Gram determinant formula for a partition $\lambda$. For the hook partitions $(l'+1,1)$ and the transpose $(l+1,1)^T$, the displayed expressions give their $C$-factors and Chebyshev expansions.

**Hook-partition formula conjecture.** Formulae for $C^{(l'+1,1)}(\alpha)$, $C^{(l+1,1)^T}(\alpha)$, $P^{(l”+1,1)}_{l”+4+k}(\alpha)$, and $P^{(l+1,1)^T}_{l+4+k}(\alpha)$ hold for all $l\geq 1$, $l'\geq 4$, and $l”\geq 2$.

The formulas were obtained from direct computations in bounded ranges and, if valid uniformly, would extend the determinant description to all the indicated hook-partition parameters.

## Summary of the result

Morris-Martin Conjecture 3.31.1 gives closed formulas for the Gram determinants of the one-cup standard modules of the Kadar-Yu algebras indexed by the hook (a+1,1) and its transpose. As printed the conjecture is false: at height a = 5 and tail length 0 the determinant has degree 174 while the printed product has degree 166. The corrected formulas are proved for both families, the ordinary hook for every a >= 2 and the transposed hook for every a >= 1, for every tail length k >= 0: in (3.3.7) the exponent of the loop variable becomes (a+3)(a+2)(a-2)/6, in (3.3.10) the missing operator is a plus, and the recurrence carries the minus sign; (3.3.8) and (3.3.9) stand as printed. Credit is for the corrected uniform theorem; the literal refutation alone would be an erratum.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
