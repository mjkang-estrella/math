# MathDB 347230: A symmetric kernel certificate for Hetyei's second-kind interval transform: a refutation of the kernel conjecture (Discrete Comput. Geom. 2024, Conjecture 39)

- Problem: https://mathdb.com/p/347230
- Source: Hetyei, arXiv:2007.07362 Conjecture 5.14 = Discrete Comput. Geom. 71 (2024) 918-944 Conjecture 39; MathDB 347230
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Hetyei347230.kernel_conjecture_false : ¬ Hetyei347230.KernelConjecture, where KernelConjecture := for all n >= 1, deg n ⊓ ker I2 = anti n, with I2(u) = u + u* + sum M(u_(1)*, u_(2)) (Theorem 32) for the Ehrenborg-Readdy coproduct and mixing operator (base cases u a v and v b u, recursion by Nat.rec, proved finite range), deg n the span of length-n ab-words and anti n = {u in deg n : u* = -u}; witnessed by an explicit 20-term symmetric degree-5 element in the kernel`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `manuscript.pdf`
- Lean source: `source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: the mixing-operator misprint is adjudicated in favour of the cited Ehrenborg-Readdy definition (hetyei-root-ruling-r1.json); citing-work coverage OpenAlex-only; the poset-level identification is a bounded degree <= 5 test, not a formal theorem trust_limits: Lean 4.34.1 core/Std and pinned mathlib trusted; leanchecker shares the installation not_claimed: a description of the kernel for general n; separate credit for 347231; priority; publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Hetyei's kernel conjecture for the second-kind interval transform on the coproduct and mixing operators. It fails at n = 5, where the kernel dimension 13 exceeds the dimension 12 of the degree-5 part, and computationally at n = 6 and 7, while holding for n <= 4; a remark records the failure of the related Conjecture 40 (MathDB 347231). The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Hetyei's kernel conjecture fails at n = 5 (dim ker I_2 = 13 > 12 = dim A_5) and, computationally, at n = 6, 7; it holds for n <= 4; 347231 (Conjecture 40) fails as a remark, without separate credit

## Body (paste into the MathDB body field)

Use the written proof in this folder: manuscript.pdf. The complete Lean source is in source-only.zip.
