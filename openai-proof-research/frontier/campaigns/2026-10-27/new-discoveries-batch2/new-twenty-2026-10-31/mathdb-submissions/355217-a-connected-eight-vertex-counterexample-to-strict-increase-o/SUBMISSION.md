# MathDB 355217: A connected eight-vertex counterexample to strict increase of outer-connected domination under the middle-graph operation

- Problem: https://mathdb.com/p/355217
- Source: Kazemnejad-Pahlavsay-Palezzato-Torielli arXiv:2206.15439 Conjecture 7.1; MathDB 355217
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `R139.MiddleOCD.mathdb_355217_connected : ¬ ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 2 ≤ Fintype.card V → ocd G < ocd (middle G), and mathdb_355217_connected' for the other empty-complement convention; with g8_value, g8_value', middle_g8_value, middle_g8_value' (IsLeast value 4). The connected negation implies the negation of the literal statement.`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `middle-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: Google Scholar, MathSciNet and zbMATH not consulted; OpenAlex lists zero citing works trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; uniqueness at order 8, the family check and the characterisation are ordinary mathematics or computation, not Lean claims not_claimed: Credit for the edgeless domain failure; Credit for the source corrections; A classification of larger counterexamples; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the conjecture of Kazemnejad, Pahlavsay, Palezzato and Torielli that the outer-connected domination number strictly increases under the middle-graph operation for every graph of order at least 2. Already for connected graphs: the 8-vertex, 11-edge graph G8 has the same value, 4, for itself and for its middle graph, under both stated conventions. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Kazemnejad, Pahlavsay, Palezzato and Torielli, arXiv:2206.15439, Conjecture 7.1 (γ̃c(G) < γ̃c(M(G)) for every graph of order n >= 2). False already for connected graphs: G8 (8 vertices, 11 edges) has γ̃c(G8) = 4 = γ̃c(M(G8)) under both conventions. Credit only for the connected negation; the edgeless failure is a domain artefact.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in middle-source.zip.
