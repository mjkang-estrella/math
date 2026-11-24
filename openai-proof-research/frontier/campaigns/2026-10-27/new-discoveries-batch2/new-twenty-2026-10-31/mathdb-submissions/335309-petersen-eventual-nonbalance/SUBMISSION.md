# MathDB 335309: The eventual non-ℓ-distance-balance conjecture for generalized Petersen graphs

- Problem: https://mathdb.com/p/335309
- Source: Štefko Miklavič and Primož Šparl, “ℓ-distance-balanced graphs”, arXiv:1702.05257 (2017), Conjecture 4.4. https://arxiv.org/abs/1702.05257
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Petersen.miklavic_sparl_4_4`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The journal text of the source could not be read and the census of citing papers is incomplete. The Lean proof is long (77 modules, 5,623 lines over four stages). Cross-model confidence 0.70, not routine 0.75. No second cross-model lane read the finished Lean: root compared the final theorem and every definition with the endpoint the Claude Opus reviewer had written (identical), and the GPT-6.1 Sol final check compared the definitions with the source and ran 55 independent breadth-first checks (k = 2 to 6, n from n_k to n_k + 10) and 54,831 arithmetic checks.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Miklavič and Šparl's Conjecture 4.4 (arXiv:1702.05257): for every k ≥ 2 and n > n_k the generalized Petersen graph GP(n,k) is not ℓ-distance-balanced for any 1 ≤ ℓ < D, and n_k is the smallest such threshold. Published work covered only k = 3, 4 and special distances. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $GP(n,k)$ be the generalized Petersen graph, let $d$ denote graph distance, and let $D$ be its diameter. For an integer $k\geq 2$, define $n_k=11$ for $k=2$, $n_k=(k+1)^2$ for odd $k$, and $n_k=k(k+2)$ for even $k\geq 4$. **The eventual non-$\ell$-distance-balance conjecture.** For any $n>n_k$, the graph $GP(n,k)$ is not $\ell$-distance-balanced for any integer $\ell$ with $1\leq\ell<D$. Moreover, $n_k$ is the smallest integer with this property.

## Summary of the result

For every k ≥ 2 and n > n_k, GP(n,k) is connected and is not ℓ-distance-balanced for any 1 ≤ ℓ < D; at n = n_k some 1 ≤ ℓ < D is balanced, so n_k is the least threshold. Published work covers only k = 3, 4 (arXiv:2309.01900) and distance 1 with weaker distance-2 bounds (Ma, Wang and Klavžar, arXiv:2407.02635). The proof gives an explicit distance formula for GP(n,k) with n ≥ k(k+2), uses the rotation and reflection automorphisms to cancel the common layer-distance profiles of a pair at distance ℓ, and reduces |W_xy| − |W_yx| to sparse 'axis pulses' whose sum is shown to be nonzero for every 1 ≤ ℓ < D by explicit witnesses; k = 2 and the sharpness at n_k are handled by finite certificates and explicit balanced distances. Lean defines GP(n,k) on Bool × ZMod n with Mathlib's SimpleGraph, W_xy as the vertices strictly closer to x, and proves connectivity for all n > n_k so that the diameter condition cannot hold vacuously.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
