# MathDB 381433: An adverse non-Q graph from the cyclic Latin square of order six

- Problem: https://mathdb.com/p/381433
- Source: D. M. Cardoso, arXiv:1811.05516 Conjecture 4.2; Optimization 69(1) (2020); D. M. Cardoso, C. J. Luz, J. Comb. Optim. 31(1) (2016) 311-326; MathDB 381433
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Adverse381433.refutation_of_source_statement : ¬ SourceConjecture (with edge hypothesis); Adverse381433.refutation : ¬ CardosoLuzConjecture; IndependentReview.refutes_stricter_source (non-complete variant, reviewer-authored)`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `adverse-latin6-draft.pdf`
- Lean source: `adverse-381433-manuscript-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; Luz 2020 (same special issue as the survey, recognition criteria) body unread; not worldwide priority remaining_literature_limits: Luz, Optimization 69(1) (2020) 131-144 body unread; Cardoso 2003 extraction corrupted; citing works not exhaustively screened trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation not_claimed: Classification of adverse non-Q graphs; Other Latin squares or parameter variants; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Cardoso-Luz conjecture that every adverse graph is a Q-graph. The graph of the cyclic Latin square of order 6, joining cells that share a row, column or symbol, has least adjacency eigenvalue -3, and its stability number 5 and convex quadratic stability number 6 both persist under deletion of every open neighbourhood, so the 36-vertex graph is adverse; the two stability numbers differ, so it is not a Q-graph. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

The cyclic Latin square graph of order 6 (cells of Z6xZ6 adjacent when sharing a row, column or symbol) has lambda_min = -3 and upsilon = 6, both unchanged after deleting every open neighbourhood, and no isolated vertices, so it is adverse; its stability number is 5 by the transversal parity obstruction, so it is not a Q-graph. This refutes Cardoso-Luz Conjecture 4.2 (survey arXiv:1811.05516, Optimization 69(1) 2020) that all adverse graphs are Q-graphs, also under the JCO 2016 'non complete' reading.

## Body (paste into the MathDB body field)

Use the written proof in this folder: adverse-latin6-draft.pdf. The complete Lean source is in adverse-381433-manuscript-source.zip.
