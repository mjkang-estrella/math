# MathDB 381805: Exact super edge-magic total strength of a seven-cycle with four leaves at one vertex

- Problem: https://mathdb.com/p/381805
- Source: Deepthi, arXiv:2212.05329v1 Conjecture 1.6 = Ars Combinatoria 159 (2024) 73-85 Conjecture 1; MathDB 381805
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Magic381805.source_refutation : ¬ Magic381805.SourceConjecture`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf` inside `source-only-proof.zip`
- Lean source: `source-only-proof.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison by root materiality ruling; reviewers held on unread older bodies remaining_literature_limits: Swaminathan-Jeyanthi 2006/2003, Avadayappan et al. 2000/2001, Figueroa-Centeno et al. 2001 original bodies unread; No all-positive-leaf counterexample trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; Exact value 26 is ordinary mathematics, not the Lean endpoint not_claimed: All-positive-leaf refutation; Replacement formula; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Deepthi's conjectured formula for the super edge-magic total strength of a cycle with leaves attached at one vertex, on its nonnegative leaf-count domain. The graph from a 7-cycle by attaching four leaves at one vertex has a labelling of constant 26, and its strength is exactly 26 by a degree rearrangement bound, against the conjectured value 2q + (n+3)/2 = 27. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

G(7;0,0,0,0,0,0,4) has an SEMT labeling with constant 26 (and sm=26 exactly by an ordinary degree-rearrangement bound), contradicting Deepthi Conjecture 1 sm(G(n;k_1..k_n)) = 2q+(n+3)/2 = 27 on its nonnegative leaf-count domain.

## Body (paste into the MathDB body field)

The archive `source-only-proof.zip` contains `paper.pdf` and the complete Lean source. Run `unzip source-only-proof.zip paper.pdf` to extract just the paper.
