# MathDB 352253: A chain-free pure YY-Delta minimum that is not minimal: a counterexample to Jeffries-Yeats Conjecture 5.1 (arXiv:2110.07764; Ann. Inst. H. Poincare D 11 (2024))

- Problem: https://mathdb.com/p/352253
- Source: Jeffries-Yeats arXiv:2110.07764v2 / Ann. Inst. H. Poincare D 11 (2024) Conjecture 5.1; MathDB 352253
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Round2.literal_negation : ¬ Literal.Conjecture51, where Conjecture51 := ∀ g, DoubledCubic g → ∀ h, PureMinimum g h → (Minimal h ↔ ¬ HasChain h), over literal loopless multigraph matrices with the source's YY-Delta and Delta-YY moves, minimality over the full equivalence class, and the illustrated edge-distinct capacity chain predicate`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: bounded citing-work and registry screens; Google Scholar and MathSciNet not consulted trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; the audit covers the 22,078 packet declarations (axioms and metadata), not a full upstream closure inventory; the chain predicate is the illustrated edge-distinct reading of the source's verbal definition and Figures 14 (a), (b), (d) not_claimed: A replacement minimality criterion; Global minimality of the order-10 graph; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Jeffries-Yeats Conjecture 5.1 for doubled 3-regular graphs, under the illustrated edge-distinct reading of its chain definition. An 18-vertex doubled cubic graph has pure YY-Delta minimum order 11, attained by 25 labelled matrices, all chain-free, yet a selected chain-free minimum reaches order 10 by seven moves, so it is not minimal. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Jeffries-Yeats Conjecture 5.1 for doubled 3-regular graphs. False: an 18-vertex doubled simple cubic graph has pure YY-Delta minimum order 11 (25 labelled minima, all chain-free under the faithful illustrated reading), and the selected minimum reaches order 10 by seven moves, so it is not minimal.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in source.zip.
