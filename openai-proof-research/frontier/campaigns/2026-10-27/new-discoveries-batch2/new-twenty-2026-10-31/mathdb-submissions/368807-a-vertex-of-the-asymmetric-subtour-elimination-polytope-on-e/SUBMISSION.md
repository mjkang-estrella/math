# MathDB 368807: A vertex of the asymmetric subtour elimination polytope on eight nodes that is adjacent to no tour

- Problem: https://mathdb.com/p/368807
- Source: arXiv:2506.10671v1 Conjecture 1, Definitions 3 and 8, Lemma 7; MathDB 368807
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `ASEP.arc_neighborhood_tour_conjecture_false : ¬ ArcNeighborhoodTourConjecture (arc space R^{n(n-1)}); ASEP.arc_counterexample; matrix-form ASEP.neighborhood_tour_conjecture_false, ASEP.counterexample; ASEP.segment_not_face, ASEP.segment_not_exposed`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `asep-368807-draft.pdf`
- Lean source: `asep-368807-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: Laurent-Poljak originals and the journal version of Deza-Indik unread; Elliott-Magwood thesis unread; 2024 Optimization Online version of the source returns 404; Padberg-Rao / Trubin TSP adjacency results unread trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation and ran without --fresh on endpoint modules; two compiler-generated _unsafe_rec helpers exist but are unreachable from endpoints not_claimed: Minimality of n=8; Results for n=6,7; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the conjecture of Vercesi, Barta, Gambardella, Gualandi and Mastrolilli that every vertex of the asymmetric subtour elimination polytope has a tour among its neighbours. At eight nodes, the fractional vertex with 19 support arcs is adjacent to none of the 5040 tours, each excluded by an integer direction certificate showing the corresponding segment is not a face; the cases n = 6, 7 remain open. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Vercesi-Barta-Gambardella-Gualandi-Mastrolilli (arXiv:2506.10671) Conjecture 1 states that every vertex of P_ASEP^n has a tour in its neighbourhood. The fractional vertex x*=X/4 of P_ASEP^8 (19 support arcs, 8 tight cuts, rank 56) is adjacent to none of the 5040 tours: for each tour an integer direction certificate shows that [x*,T] is not a face. The conjecture fails at n=8; n=6,7 remain open.

## Body (paste into the MathDB body field)

Use the written proof in this folder: asep-368807-draft.pdf. The complete Lean source is in asep-368807-source.zip.
