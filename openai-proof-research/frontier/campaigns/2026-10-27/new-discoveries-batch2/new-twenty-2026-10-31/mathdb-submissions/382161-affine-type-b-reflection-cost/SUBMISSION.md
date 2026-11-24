# MathDB 382161: The cost formula in the affine Weyl group of type B (Lewis–Tenner Conjecture 4.2)

- Problem: https://mathdb.com/p/382161
- Source: Joel Brewster Lewis and Bridget Eileen Tenner, “Bargain hunting in a Coxeter group”, arXiv:2302.04404 (2023), Conjecture 4.2. https://arxiv.org/abs/2302.04404
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `AffineB.lewis_tenner_4_2`, `AffineB.lewis_tenner_4_2_lower`, `AffineB.lewis_tenner_4_2_attained`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Every factor of a factorization must be a reflection of the type B group itself; the source's pair test read alone would admit single sign flips outside the group, under which the formula fails (for example at [−1, −2]); Lean enforces membership, which the reviewers judged to be the source's meaning. Lean states the formula doubled (costs and displacement in half units), which is exactly twice the printed formula; the block difference is proved non-negative, so no truncated subtraction is involved. The written proof by Claude Opus needed two local corrections found by the GPT-6.2 Sol review (negation reverses displacement signs; cut balance requires oddness), which the Lean proof and the paper follow. The journal version of the source was not read (reviewer's probability that it settles the conjecture: 0.01). Proof and first (same-model) review are by Claude Opus 5.5 (two lanes: the lower-bound lemma from pool 199, the upper bound from a continuation lane); the cross-model review (not routine 0.74), the Lean code and the final check (a separate lane) are by GPT-6.2 Sol, so the final check is by the same model family as the Lean packager.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Lewis and Tenner (arXiv:2302.04404, Conjecture 4.2) conjectured that in the affine Weyl group of type B the reflection cost of w equals dis(w)/2 + bl_C(w) − bl_B(w). The lower bound comes from a crossing-count lemma that charges one extra unit to each odd block; the upper bound from an explicit greedy factorization that switches partners to avoid closing odd blocks. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $w$ be an affine signed permutation in $\widetilde{S}^B_n$. An integer $j\in[n-1]$ is **good** if $w$ restricts to a bijection from $\pm[j]$ to itself, and it is **very good** if this restriction is an even-signed permutation. Define

$$
\operatorname{bl}^{\widetilde{C}}(w)=1+\#\{\text{good values for }w\},\qquad \operatorname{bl}^{\widetilde{B}}(w)=1+\#\{\text{very good values for }w\}.
$$

Here $\$(w)$ and $\operatorname{dis}(w)$ denote the quantities defined for affine signed permutations in the paper. **The affine type B conjecture.** If $w\in\widetilde{S}^B_n$, then

$$
\$(w)=\frac{1}{2}\operatorname{dis}(w)+\operatorname{bl}^{\widetilde{C}}(w)-\operatorname{bl}^{\widetilde{B}}(w).
$$

This conjecture extends the finite-type formula to affine type $\widetilde{B}$. If true, it would imply $\$(w)-\operatorname{dis}(w)/2\leq n$ for all $w\in\widetilde{S}^B_n$; the corresponding boundedness behavior is contrasted with the affine type $\widetilde{D}$ case.

## Summary of the result

The conjecture holds for every n: the cheapest way to write an affine signed permutation w of type B as a product of reflections of that group, where a reflection costs its depth, costs dis(w)/2 + bl_C(w) − bl_B(w). Lower bound: every reflection changes the displacement by at most twice its cost, and a crossing-count lemma shows that each good cut that is not very good (an odd block) forces one extra unit of cost, because a product of reflections of the type B group restricted to a block that is preserved by all of them has an even number of sign changes. Upper bound: a greedy rule that always applies an efficient swap, and switches the partner of the swap whenever the obvious choice would close an odd block, reaches the identity at exactly that cost; its termination and invariants are proved. The source proves the analogous formulas where no branching occurs and in finite type D; in affine type B no depth formula was available. Lean defines the group as permutations of the integers with the periodicity, negation and parity conditions, takes costs over lists of reflections each of which belongs to the group, and proves that the doubled formula dis(w) + 2(bl_C(w) − bl_B(w)) is the least element of the set of doubled costs, so the minimum is attained.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
