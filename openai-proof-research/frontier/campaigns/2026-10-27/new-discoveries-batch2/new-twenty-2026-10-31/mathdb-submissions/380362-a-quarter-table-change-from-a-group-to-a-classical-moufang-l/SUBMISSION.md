# MathDB 380362: A quarter-table change from a group to a classical Moufang loop of order 16

- Problem: https://mathdb.com/p/380362
- Source: Drapal-Vojtechovsky, Moufang loops that share associator and three quarters of their multiplication tables, Rocky Mountain J. Math. 36 (2006) 425-455; arXiv:math/0701710 Conjecture 11.2; MathDB 380362
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Loop380362.source_refutation : ¬ Loop380362.SourceClaim`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: Typeset journal text not compared (arXiv posting postdates it); Bounded loop-theory literature search; MathDB/Palomar inaccessible trust_limits: Prebuilt upstream Mathlib oleans trusted; no source-to-olean attestation; leanchecker shares the installation not_claimed: New loop or isomorphism type; Conjecture 11.1 (strict quarter); Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the unrestricted associator-distance bound, Drapal-Vojtechovsky Conjecture 11.2, that two Moufang loop operations on a common set of N elements with inequivalent associators have table distance at least 3N^2/8. The elementary abelian group of order 16 and the classical cubic code loop on the same 16 labels differ in exactly 64 of the 256 table entries and have associator images of sizes 1 and 2, and 64 is below 96. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

F_2^4 and the cubic code loop on F_2^3 x F_2 are Moufang loops with common identity, associators with images of size 1 and 2 (inequivalent under pointed, unpointed and independent bijective readings), and table distance 64 < 3*16^2/8 = 96; refutes Drapal-Vojtechovsky Conjecture 11.2 in its stated unrestricted scope.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in source-only.zip.
