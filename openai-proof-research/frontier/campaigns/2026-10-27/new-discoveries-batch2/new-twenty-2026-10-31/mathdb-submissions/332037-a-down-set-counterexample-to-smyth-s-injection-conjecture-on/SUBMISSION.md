# MathDB 332037: A down-set counterexample to Smyth's injection conjecture on compositions (Conjecture 1.5 of arXiv:1512.04084; Order 35 (2018))

- Problem: https://mathdb.com/p/332037
- Source: Smyth arXiv:1512.04084v1 Conjecture 1.5 (Order 35 (2018) 393-402); MathDB 332037
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Smyth1512.not_conjecture15 : ¬ Smyth1512.Conjecture15, where Conjecture15 := ∀ A a B b : ℕ, B ≤ A → b ≤ a → ∃ γ : (U A b × U B a) → (U A a × U B b), Function.Injective γ ∧ ∀ x, Dom (concat x.1.1 x.2.1) (concat (γ x).1.1 (γ x).2.1); U m n = compositions Fin m → ℕ of sum n; Dom = dominance (equal sums, all prefix sums) of non-increasing rearrangements; concat = Fin.append`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: post-refereeing Order printed body unread (the author-hosted submitted manuscript retains the conjecture as Conjecture 6); bounded citing-work screens; some citing bodies inaccessible; Google Scholar and MathSciNet not consulted trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; the audit covers the 115 packet declarations (axioms and metadata), not a full upstream closure inventory; the matching value 4407, the passing ranges and the (3, b+1, 2, b) family are supporting computation, not Lean claims not_claimed: The (3, b+1, 2, b) failures for b = 19..43; Minimality of the parameters; Any refutation of Smyth's TN2 product inequality or probabilistic characterization; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Smyth's injection conjecture that for A >= B >= 0 and a >= b >= 0 there is a dominance-decreasing injection from the product of uniform downsets U^A_b x U^B_a to U^A_a x U^B_b. At (A,a,B,b) = (3,20,2,19), the down-set of 8 explicit partitions of 39 contains 1137 rearranged concatenations of domain elements but only 1134 target elements. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Smyth's Conjecture 1.5: for all A ≥ B ≥ 0 and a ≥ b ≥ 0 there is a dominance-decreasing injection U^A_b × U^B_a → U^A_a × U^B_b. False at (A, a, B, b) = (3, 20, 2, 19): the down-set of 8 explicit partitions of 39 contains the rearranged concatenations of 1137 domain elements but only 1134 target elements.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in source-only.zip.
