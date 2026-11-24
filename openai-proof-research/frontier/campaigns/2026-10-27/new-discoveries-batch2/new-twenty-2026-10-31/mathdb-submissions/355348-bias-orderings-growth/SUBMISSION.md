# MathDB 355348: Growth conjecture for the number of orderings of congruence-class biases

- Problem: https://mathdb.com/p/355348
- Source: Faye Jackson and Misheel Otgonbayar, “Unexpected Biases between Congruence Classes for Parts in k-indivisible Partitions”, arXiv:2207.06365 (2022), Conjecture 1.5; J. Number Theory 248 (2023). https://arxiv.org/abs/2207.06365
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `BiasGrowth.conjecture_355348`, `BiasGrowth.conjecture_355348_strict`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The o(t) half is close to routine (about a dozen lines from the source's lemmas); the content is the class-recovery lower bound (cross-model reviewer: not routine 0.60). The Lean proves weaker rates (t^{1/4}/80 lower; φ(t)(t/H + 2H^2 + 2) upper) than the written proof's t^{1/3} and √t log t, which the paper gives as unformalized remarks; both little-o statements are proved exactly. The one non-Lean link is the source's Corollary 1.2 (the relation between partition counts and score comparisons). The journal text (J. Number Theory 2023) was not read (refused). The Lean was written by a GPT-6.1 Sol lane and packaged by a Claude Opus 5.5 lane; the final check was by a separate Opus lane (same model family as the packager) because GPT-6.1 Sol hit its usage limit; a Sol re-check after 2026-11-26 is advisable.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Jackson and Otgonbayar's growth conjecture (arXiv:2207.06365, Conjecture 1.5): the number O(t) of orderings of congruence-class biases satisfies O(t)/φ(t) = o(t) and log t = o(O(t)/φ(t)). The key step: the ordering for k reveals k mod t through a unique maximum of right inversions, forcing many distinct orderings. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $\mathscr{O}(t)$ denote the number of possible orderings arising from the biases among congruence classes for $k$-indivisible partitions, and let $\varphi(t)$ be Euler's totient function. **Growth conjecture.** As $t\to\infty$, we have $\mathscr{O}(t)/\varphi(t)=o(t)$ and $\log t=o\left(\mathscr{O}(t)/\varphi(t)\right)$.

## Summary of the result

Both growth assertions hold. The orderings are determined by the second-order scores −ψ(r/t) + ψ(ρ(r)/t)/k of the source (ρ(r) the residue of k⁻¹r). The upper bound uses the source's own score formula: for each residue class of k the ordering changes only boundedly often before it settles, giving O(t) ≤ φ(t)(⌊t/H⌋ + 2H² + 2) for every H, hence o(t·φ(t)). The lower bound carries the new idea: for k = mt + q the label q is the unique label with the most right inversions, so the ordering reveals k mod t, and a counting argument forces a new ordering at every consecutive quotient m up to a power of t; Lean proves O(t)/φ(t) ≥ t^{1/4}/80 for large t (the written proof gives t^{1/3}). Lean defines ψ as Mathlib's digamma (with the series bridge proved), counts orderings over all k ≥ 2 coprime to t with no cap, and proves the statement for every relation family compatible with the score comparisons, which is how the source's Corollary 1.2 links its partition counts to the scores; the later no-ties theorem is not needed.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
