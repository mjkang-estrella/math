# MathDB 342414: A cubic counterexample to edge-pattern convex domination

- Problem: https://mathdb.com/p/342414
- Source: F. Pirot, J.-S. Sereni, arXiv:1904.05618 v1/v6 Conjecture 2; SIAM J. Discrete Math. 35(4) 2021; MathDB 342414
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `EdgePattern.TreeModelsR5.refutation : ¬ EdgePattern.Conjecture2.{0}`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `edgepattern-draft.pdf`
- Lean source: `edgepattern-source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: final SIAM body unread (publisher access); parallel Lagrangian heuristic body inaccessible (403); an edge/vertex-coloured-graphs thesis read at metadata level only trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; the depth-at-most-2 robustness (28/27) is ordinary mathematics, not a Lean endpoint; the endpoint is at universe 0 not_claimed: Any change to fractional colouring bounds; Refutation for other (d, r); Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Pirot-Sereni edge-pattern convex domination conjecture, at d = 3, r = 2. The 8-vertex 3-regular pattern P of depth 2 and girth 6, with exponent vector (2/5,14/5,4/5), has value 67027/67500 below 1 at the weight alpha = (1/1000,7/27,1/3), while every acyclic 3-regular depth-2 pattern among the 81 leaf-count forms has value at least 3001/3000; the source's optimized bounds are unaffected. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Pirot-Sereni (arXiv:1904.05618; SIAM J. Discrete Math. 35(4) (2021) 2815-2843) Conjecture 2, also Conjecture 1.5.1 of Pirot's 2019 thesis, is false at d = 3, r = 2. The 8-vertex edge-rooted pattern P (root edge 01; edges 01,02,03,15,17,34,46,56: a 6-cycle with two pendants) is 3-regular, of exact depth 2 and girth 6, with e(P) = (2/5,14/5,4/5). With alpha = (1/1000,7/27,1/3), alpha.e(P) = 67027/67500 < 1, while every acyclic 3-regular depth-2 edge-rooted pattern (all 81 leaf-count forms) has alpha.e(T) >= 3001/3000. So no convex combination of tree constraints is weaker than e(P). The source's optimized bounds (Lemma 10) are unaffected.

## Body (paste into the MathDB body field)

Use the written proof in this folder: edgepattern-draft.pdf. The complete Lean source is in edgepattern-source-only.zip.
