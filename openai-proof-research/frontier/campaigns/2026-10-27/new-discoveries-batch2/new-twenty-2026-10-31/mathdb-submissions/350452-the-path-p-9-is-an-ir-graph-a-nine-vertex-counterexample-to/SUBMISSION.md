# MathDB 350452: The path P_9 is an IR-graph: a nine-vertex counterexample to the Mynhardt-Roux non-IR conjecture for paths

- Problem: https://mathdb.com/p/350452
- Source: Mynhardt-Roux, Irredundance Graphs, arXiv:1812.03382 (Discrete Appl. Math. 2022), Conjectures 1 and 2; Mynhardt-Roux, Irredundance Trees of Diameter 3, arXiv:2104.09004 (Discrete Math. 2022), Open Problems Conjecture 1; MathDB 350452
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `IR350452.conjecture_false : ¬ IR350452.Conjecture, where Conjecture := (forall n >= 3, ¬ IsIRGraph (pathGraph n)) ∧ (forall n >= 5, ¬ IsIRGraph (cycleGraph n)), IsIRGraph H := there are a finite vertex type V and G : SimpleGraph V with H ≃g IRGraph G, IRGraph G has the IR(G)-sets (irredundant sets of maximum cardinality, private neighbours via closed neighbourhoods) as vertices and the swap adjacency D' = insert v (D.erase u) with uv in E(G); witnessed by an explicit isomorphism pathGraph 9 ≃g IRGraph G9`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `manuscript.pdf`
- Lean source: `source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: DAM 2022 and DM 2022 versions of record unread (ScienceDirect denied; all arXiv versions read); bounded citing-work coverage (OpenAlex 7 citing works) trust_limits: Lean 4.34.1 core/Std and pinned mathlib trusted; leanchecker shares the installation not_claimed: part (ii) on cycles; whether P_6 is an IR-graph; infinitely many path IR-graphs; priority; publication; separate credit for the independent-IR-set problem
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Mynhardt-Roux conjecture that no iterated IR-construction yields a path, in its part (i). The path P_9 on nine vertices is an IR-graph; computationally, 9 is the smallest order of a graph whose IR-graph is a path of order at least 3, and P_7, P_8 and P_9 all occur at order 9. Part (ii), for cycles, and the case P_6 remain open. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

part (i) of the conjecture (paths) is false: P_9 is an IR-graph; computationally 9 is the minimum order of a graph whose IR-graph is a path of order >= 3 and P_7, P_8, P_9 occur at order 9; part (ii) (cycles) and P_6 remain open

## Body (paste into the MathDB body field)

Use the written proof in this folder: manuscript.pdf. The complete Lean source is in source.zip.
