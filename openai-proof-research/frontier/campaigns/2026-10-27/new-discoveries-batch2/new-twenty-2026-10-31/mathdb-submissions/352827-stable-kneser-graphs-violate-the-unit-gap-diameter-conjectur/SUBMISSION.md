# MathDB 352827: Stable Kneser graphs violate the unit-gap diameter conjecture: D(SG(27,12)) ≥ 8 while D(SG(28,12)) ≤ 6

- Problem: https://mathdb.com/p/352827
- Source: Ledezma-Pastine-Torres-Valencia-Pabon arXiv:2112.01884v2 Conjecture 2; MathDB 352827
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Schrijver.mathdb_352827 : ¬ SchrijverUnitGap (the literal Conjecture 2: for all naturals k, r with 2 ≤ r ≤ k−2, D(SG(2k+r,k)) − D(SG(2k+r+1,k)) ∈ {0,1}, with SG(n,k) the Schrijver graph on cyclically 2-stable k-subsets of Fin n with disjointness adjacency and D the Mathlib diameter, connectivity proved)`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `schrijver-source-r5.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: DAM journal body unread (ScienceDirect not used; HAL no deposit; CONICET 403); citing-work census incomplete trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; k = 13 exact-diameter table entries are ordinary computation, not Lean claims not_claimed: The k = 10, r = 2 Theorem 6 correction; Exact diameters as Lean claims (Lean proves D(SG(27,12)) ≥ 8 and D(SG(28,12)) ≤ 6; the exact values 8 and 6 are ordinary computation); Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the unit-gap diameter conjecture of Ledezma, Pastine, Torres and Valencia-Pabon for stable Kneser graphs. The diameter of SG(27,12) is at least 8, by an explicit pair with a distance-labelling certificate, while breadth-first certificates over 116 rotation-orbit representatives give diameter at most 6 for SG(28,12), a drop of 2; the source's Theorem 6, used elsewhere, is itself incorrect. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Ledezma, Pastine, Torres, Valencia-Pabon, arXiv:2112.01884v2 (DAM 350 (2024) 15-30), Conjecture 2. False at k = 12, r = 3: D(SG(27,12)) ≥ 8 by an explicit pair (masks 21669205, 39144021) with a distance-labelling certificate, and D(SG(28,12)) ≤ 6 by BFS-tree certificates over 116 rotation-orbit representatives; the drop is 2. Independent of the source's Theorem 6 (found false; the r = 2 route was a source-internal correction and is not credited).

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in schrijver-source-r5.zip.
