# MathDB 378395: An explicit non-collapsing facet of the 4 x 4 x 5 marginal cone

- Problem: https://mathdb.com/p/378395
- Source: Eriksson-Fienberg-Rinaldo-Sullivant, J. Symbolic Comput. 41 (2006), Conjecture 14; arXiv:math/0405044 conj:col; MathDB 378395
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `MathDB378395.Main.collapsing_conjecture_false : ¬ CollapsingConjecture`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `source-only-proof.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison by root ruling; reviewers held on Schroeter 2017/2018 enumeration (orbit counts, no representatives) remaining_literature_limits: Schroeter enumeration of coarsest product subdivisions may contain this subdivision (no explicit match); Full Dr(3,8)/Dr(4,8) data not compared; MathDB/Palomar inaccessible trust_limits: Prebuilt upstream Mathlib oleans trusted; no source-to-olean attestation; leanchecker shares the installation; 64 GiB address space used with 6 GiB private-RSS guard not_claimed: Classification of non-collapsing facets; Minimal counterexample; Tropical bridge novelty; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Eriksson-Fienberg-Rinaldo-Sullivant collapsing conjecture for facets of no-three-way-interaction marginal cones, Conjecture 14. An integral functional exposes a facet of the 4 by 4 by 5 cone, of dimension 43 inside 44, whose five layers have pairwise distinct zero patterns, so the facet is not the pullback of any facet under a state map to the 4 by 4 by 4 cone. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

An integral functional exposes a facet of the no-three-way-interaction marginal cone P^{4,4,5} (dimension 43 in a cone of dimension 44) whose five layers have pairwise distinct zero patterns, so it is not a pullback under any state maps to 4x4x4; refutes Eriksson-Fienberg-Rinaldo-Sullivant Conjecture 14.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in source-only-proof.zip.
