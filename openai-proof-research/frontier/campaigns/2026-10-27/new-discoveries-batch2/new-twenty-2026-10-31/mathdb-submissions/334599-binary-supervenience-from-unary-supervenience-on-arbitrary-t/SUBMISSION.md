# MathDB 334599: Binary supervenience from unary supervenience on arbitrary ternary frames

- Problem: https://mathdb.com/p/334599
- Source: Jie Fan, arXiv:1611.04740 Conjecture 15 and Section 7.3; Notre Dame J. Formal Logic 60(2) (2019) 283-309; Humberstone, Logic and Logical Philosophy 28 (2019) 3-135, pp. 16-17; MathDB 334599
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Supervenience.literal_conjecture_false : ¬ HierarchyConjecture; Supervenience.hierarchy_conjecture_false : ¬ StrictAtOne`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `supervenience-draft.pdf`
- Lean source: `source-only-proof.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; specialist literature asserts the opposite; not worldwide priority remaining_literature_limits: NDJFL 2019 journal text unread (challenge); Yang/Vaananen, Ciardelli thesis, older Humberstone works not exhaustively covered trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation not_claimed: Novelty of the Boolean-cell technique; Results on other frame classes; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Fan Conjecture 15, the strict hierarchy between binary and unary supervenience. On arbitrary ternary frames, every formula of the language with two determining inputs is equivalent to one with a single determining input, via the guard G(A,B) = D1(A; A and B) on the four Boolean cells; the relativized agreement formula is likewise definable, correcting the recorded Humberstone undefinability assertion. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

On arbitrary ternary frames every formula of the language with two determining inputs is equivalent to one with a single determining input (guard G(A,B)=D1(A; A and B) on the four Boolean cells), so Fan Conjecture 15 (strict hierarchy) fails at n=1; the Section 7.3 relativized agreement is definable; Humberstone 2019 pp. 16-17 undefinability assertion is corrected.

## Body (paste into the MathDB body field)

Use the written proof in this folder: supervenience-draft.pdf. The complete Lean source is in source-only-proof.zip.
