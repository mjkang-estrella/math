# MathDB 365943: There is no cubic 8-circulant nut graph: completing the existence classification of cubic polycirculant nut graphs

- Problem: https://mathdb.com/p/365943
- Source: N. Bašić and I. Damnjanović, arXiv:2411.16904v1 Conjecture 16; Comput. Appl. Math. (2025), DOI 10.1007/s40314-025-03218-7, Conjecture 1; MathDB 365943
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Nut8.no_cubic_8circulant_nut : Nut8.Target, where Target := ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj], ¬ (Cubic G ∧ Nut G ∧ Circulant 8 G); Nut: at least two vertices, real adjacency kernel of dimension one containing a full vector; Circulant l: an automorphism whose integer-power orbits number l, all of equal size`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `nut-draft.pdf`
- Lean source: `nut-r7q-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: Nut digraphs body denied at its repository route and unread; later degree/quartic versions and the final published degree body not independently cleared; citing-work inventory incomplete trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; Python enumeration and PDF generation outside the logical trust base not_claimed: The finer degree-order-orbit problem (Problem 17 of the preprint); Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: there is no cubic 8-circulant nut graph, the last open case in the Basic-Damnjanovic classification of cubic polycirculant nut graphs. One kernel character gives an 8 by 8 quotient matrix of nullity exactly one with nonzero diagonal cofactors, and a kernel-checked catalogue of 194 connected subcubic supports, with isomorphism and exact determinant or zero-cofactor certificates, excludes every case, for all orbit sizes. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Bašić and Damnjanović, On cubic polycirculant nut graphs, arXiv:2411.16904v1 Conjecture 16 = Conjecture 1 of the published version (Comput. Appl. Math. 2025). Their Theorem 2 excludes l in {1,2,4,5} and constructs cubic l-circulant nut graphs for l in {3,6,7} and l >= 9; l = 8 was the only open case. Proof: a single kernel character on semiregular orbit coordinates gives a symmetric signed integral 8x8 quotient with nullity exactly one (injective lift) and nonzero diagonal cofactors; cubicity forces a local grammar; an inductive kernel-checked catalogue of 194 connected subcubic supports with 1,722 isomorphism certificates, 669 augmentations and tree switching reduce to 9,172 signed matrices, each excluded by an exact determinant (8,208) or zero principal cofactor (964) certificate. Valid for all orbit sizes m, without bounding graph order.

## Body (paste into the MathDB body field)

Use the written proof in this folder: nut-draft.pdf. The complete Lean source is in nut-r7q-source.zip.
