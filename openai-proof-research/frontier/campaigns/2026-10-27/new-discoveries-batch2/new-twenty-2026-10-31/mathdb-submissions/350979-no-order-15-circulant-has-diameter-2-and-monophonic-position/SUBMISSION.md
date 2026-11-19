# MathDB 350979: No order-15 circulant has diameter 2 and monophonic position number 2

- Problem: https://mathdb.com/p/350979
- Source: J. Tuite, E. J. Thomas, U. Chandran S. V., arXiv:2106.06827v3 Conjecture 4.5; MathDB 350979
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Circulant350979.source_refutation : ¬ Circulant350979.SourceClaim, where SourceClaim := ∀ n ≥ 11, ∃ J : Set (ZMod n), (circulantGraph J).diam = 2 ∧ mpNumber (circulantGraph J) = 2`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `circulant-draft.pdf`
- Lean source: `circulant-source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: Ars Math. Contemp. journal body unread (403, not retried); citing-literature census not exhaustive trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; exact mp = 6 and the 11..40 coverage are supplementary computations, not part of the Lean endpoint not_claimed: The corrected conjecture for n >= 11, n != 15; Any coverage above order 40; Novelty of the C5[3K1] graph or its mp-number (product formula, arXiv:2412.09837); Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Tuite-Thomas-Chandran conjecture that for every n >= 11 there is a circulant graph of order n with diameter 2 and monophonic position number 2. Every diameter-2 circulant on 15 vertices has monophonic position number at least 3: 109 of the 128 jump masks contain a triangle, 17 more fail the distance bound, and the last two give a C_5 blow-up whose exact value is 6. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Tuite-Thomas-Chandran (arXiv:2106.06827v3; Ars Math. Contemp. 2025) Conjecture 4.5 asserts that for every n >= 11 there is a circulant graph of order n with diameter 2 and monophonic position number 2 (still listed as open in the survey arXiv:2501.19385 v5, August 2026). False at the interior order 15. Every diameter-2 circulant of order 15 contains a triangle, or is C5[3K1] (jumps {1,4,6} or {2,3,7}) with three open twins; both kinds of triple are mp-sets. Verified circulant examples exist at every other order 11..40 (supplementary; not claimed beyond).

## Body (paste into the MathDB body field)

Use the written proof in this folder: circulant-draft.pdf. The complete Lean source is in circulant-source-only.zip.
