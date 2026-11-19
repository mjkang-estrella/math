# MathDB 343790: Equal degree and type do not determine a code-loop representation

- Problem: https://mathdb.com/p/343790
- Source: Pires-Grishkov-Rasskazova, Representations of code loops by binary codes, arXiv1909.05143v1 (9Sep2019), Definitions2-3 and Conjecture1; 2026 revised/extended body arXiv2601.02332v1 (5Jan2026) compared; omission of explicit conjecture not treated as correction/retraction
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `literal2019_refuted_on_fin50; full50_counterexample; separately common_isMoufangLoop`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `code-loop-proof.pdf`, `code-loop-proof.md`
- Lean source: `code-loop-source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded primary-body/current-registry/chronology/subsumption review, not worldwide priority certification. prior_limits: 2018 original publisher body inaccessible and not retried; original1986/1990 bodies and thesis not fully read; Authenticated narrow rank-four thesis attribution is not an identified equal-type representation-nonuniqueness theorem; Independent realization author PDF theorem/proof read, final publication/date not authenticated; No complete registry-tree/history/citation or worldwide semantic clearance; Live MathDB comments/solutions not cleared trust_limits: Pinned prebuilt upstream and mathematical truth trusted; no full upstream rebuild/attestation; leanchecker shares pinned Lean installation; Sampled RSS/CPU are not continuous cgroup or aggregate concurrency bounds; Audit metaprogramming is outside production and not a new theorem premise not_claimed: Minimal representation or center-order-two/rank3-4 uniqueness refutation; New underlying Moufang loop or separate credit for the existing loop-construction family; Worldwide priority/publication/journal peer review; Every IR artifact has a kernel proof body; IsMoufangLoop is an explicit conjunct of full50_counterexample
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the conjecture that the degree and type of a binary linear code determine the Moufang loop it represents. Two rank-seven full-support reduced doubly-even codes on 50 coordinates, each of sorted type fifteen ones and seven fives, represent the same explicitly nonassociative Moufang loop through genuine sign-respecting multiplicative bijections, yet no permutation of the 50 coordinates carries one code to the other. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Two actual rank-seven full-support reduced doubly-even binary subspaces on Fin50, each with sorted type fifteen ones/seven fives, represent the SAME explicitly nonassociative Moufang loop by genuine source-sign multiplicative bijections, but no arbitrary Fin50 coordinate permutation carries one code to the other. Refutes the broad printed2019Conjecture1, with all factor, weight, quotient-type, sign, rank and transport bridges included.

## Body (paste into the MathDB body field)

Use the written proof in this folder: code-loop-proof.pdf. The complete Lean source is in code-loop-source-only.zip.
