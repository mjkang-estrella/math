# MathDB 352297: Great-circle thrackleable trees are a proper subclass of augmented caterpillars

- Problem: https://mathdb.com/p/352297
- Source: Karen Collins and Cleo Roberts, “Great-circle Tree Thrackles”, arXiv:2110.09679 (2021); Discrete Math. 346(1) (2023) 113121; Conjecture 3.4. https://arxiv.org/abs/2110.09679
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `GC.mathdb_352297`, `GC.mathdb_352297_strict`, `GC.mathdb_352297_containment`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Both halves are stated for trees with at least three vertices: under the literal Definition 3.1, K₁ and K₂ are drawable but not augmented caterpillars (proved in Lean), so the source's own Theorem 3.2 needs the same restriction; the open strictness half is unaffected. The MathDB paraphrase omits 'general position', which the source assumes by convention. The strictness half is a certified finite computation by the standard oriented-matroid-plus-SAT method in its spherical setting; once the encoding exists a SAT sweep finds such trees quickly. Cross-model reviewer: not routine 0.55 (at the floor root uses for counting); final checker 0.5–0.55, COUNTS as a borderline, modest result. The conjecture has no citing works, so 'open' is weak evidence of difficulty. Journal text (Discrete Math. 2023) unread. Because GPT-6.1 Sol hit its usage limit, the Lean packaging and the final check were both by Claude Opus 5.5 lanes (the cross-model review is the Opus review of a Sol proof). The same conjecture is MathDB 247589; it counts once.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Collins and Roberts (arXiv:2110.09679, Conjecture 3.4) conjectured that the great-circle thrackleable trees form a proper subclass of the augmented caterpillars. A 14-vertex augmented caterpillar (an edge with three pendant 2-paths at each end) has no great-circle thrackle drawing in general position, certified by a chirotope sign encoding and an unsatisfiability certificate; with the authors' containment theorem (re-proved the same way) the containment is proper. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

A **great-circle thrackleable tree** is a tree admitting a thrackle drawing on the sphere in which the edges are great-circle arcs. An **augmented caterpillar** is the graph class defined in the source. **Conjecture on great-circle thrackleable trees and augmented caterpillars.** The class of great-circle thrackleable trees is properly contained in the class of augmented caterpillars. The conjecture is proposed as a further restriction on the class of trees that can be great-circle thrackleable; the source leaves it open and notes that crossing orientations may be relevant to proving or disproving it.

## Summary of the result

The conjecture holds: every great-circle thrackleable tree (with at least three vertices) is an augmented caterpillar, and the containment is proper. The open half is strictness. The 14-vertex tree T formed by an edge 01 with three pendant 2-paths at each of 0 and 1 is an augmented caterpillar under every reading of the source's Definition 3.1 (its legs are disjoint paths), but it has no great-circle thrackle drawing in general position. The proof (GPT-6.1 Sol) encodes a drawing by the signs of 3×3 determinants of the vertex vectors (a rank-3 chirotope), imposes the 3-term Grassmann–Plücker relations and an exact table saying when a short or long great-circle arc meets another exactly once, and refutes the resulting 162,578-clause formula with an LRAT certificate; the containment half (the source's Theorem 3.2) is re-proved the same way from a certificate that the 3,3,3 spider is undrawable. Lean defines drawings on the unit sphere of ℝ³ in general position, short and long arcs, the thrackle condition (every two distinct edges meet in exactly one point) and the source's Definition 3.1 with legs, generates the input clauses by a Lean function of the tree, proves that every geometric drawing satisfies all of them, and checks both certificates by `decide +kernel` through a reflective RUP checker proved sound in Lean (no native_decide, no bv_decide, no ofReduceBool). T is the tree the source's own Conjecture 3.5 predicts is undrawable; that conjecture is neither used nor proved.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
