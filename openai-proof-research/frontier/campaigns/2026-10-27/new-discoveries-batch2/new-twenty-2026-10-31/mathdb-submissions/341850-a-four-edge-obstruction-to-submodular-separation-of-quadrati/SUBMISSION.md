# MathDB 341850: A four-edge obstruction to submodular separation of quadratic Boolean monomial images: a counterexample to Brakensiek-Gopi-Guruswami Conjecture 3.33 (arXiv:1902.04740; ECCC TR19-013)

- Problem: https://mathdb.com/p/341850
- Source: Brakensiek-Gopi-Guruswami arXiv:1902.04740v1 / ECCC TR19-013 Conjecture 3.33 (SIAM J. Comput. 51(3) (2022) 577-626 as listed by the authors); MathDB 341850
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Separation.source_existence_refuted : ¬ Separation.SeparationExistence, where SeparationExistence := for all d r with r <= d there is f : Point d -> Z that is submodular on allowed points (union/intersection), <= -1 on every monomial image phi r X (filtered powerset, including the empty monomial) and >= 0 on every allowed non-image point; Conjecture 3.33 (which also asks for poly(n)-time evaluation) implies SeparationExistence`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `lean-packet.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority; no new general obstruction claimed remaining_literature_limits: SICOMP 2022 version of record unread; bounded citing-work coverage trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; the poly-time clause is not formalized (refuting bare existence suffices) not_claimed: A new general obstruction; Hardness or tractability of SUBMOD-MIN-MOD_M; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Brakensiek-Gopi-Guruswami Conjecture 3.33 on submodular separation of monomial images. At (r,d) = (2,5), no integer-valued, indeed no real-valued, submodular function on the 16-point Boolean cube is negative exactly on the degree-2 monomial image of the 5-dimensional Boolean cube. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Conjecture 3.33 is false at (r,d) = (2,5): no integer- (indeed real-) valued submodular function on {0,1}^16 is negative exactly on the degree-2 monomial image of {0,1}^5.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in lean-packet.zip.
