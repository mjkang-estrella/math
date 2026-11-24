# MathDB 321730: The locating chromatic numbers of K_m □ C_n and K_m □ P_n agree for m ≥ 7 and n ≥ 4 (Behtoei–Omoomi Conjecture 3)

- Problem: https://mathdb.com/p/321730
- Source: Ali Behtoei and Behnaz Omoomi, “On the Locating Chromatic Number of the Cartesian Product of Graphs”, arXiv:1106.3453 (2012); Ars Combin. 126 (2016); Conjecture 3. https://arxiv.org/abs/1106.3453
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Locating321730.mathdb_321730`, `Locating321730.locChrom_KC`, `Locating321730.locChrom_KP`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The conjecture says 'sufficiently large' without thresholds; the result gives the thresholds m ≥ 7 and n ≥ 4 and says nothing about smaller cases. The path formula is Behtoei and Omoomi's Theorem 2 (valid for m ≥ 3, n ≥ 2); the contribution is the cycle formula. Closest related work: Ghanbari and Mojdeh (2024) treat the same family for the stronger neighbour-locating invariant and give an m + 1 colouring for triangles. ProbXiv was unavailable to the final check. Proof and first (same-model) review are by Claude Opus 5.5 (the same-model review had rated it 0.5); the cross-model review (not routine 0.76), the Lean code and the final check (a separate lane) are by GPT-6.2 Sol, so the final check is by the same model family as the Lean packager.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Behtoei and Omoomi (arXiv:1106.3453, Conjecture 3) conjectured that for sufficiently large m and n the Cartesian products K_m □ C_n and K_m □ P_n have the same locating chromatic number. For all m ≥ 7 and n ≥ 4 both equal m + 1 if n ≤ m + 1 and m + 2 otherwise; the path value is the authors' theorem and the cycle value is new. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $K_m$ be the complete graph, and let $C_n$ and $P_n$ denote the cycle and path on $n$ vertices, respectively. Write $\square$ for the Cartesian product and $\chi_L$ for the locating chromatic number. **Locating chromatic number conjecture for products with cycles and paths.** If $m$ and $n$ are sufficiently large, then

$$
\chi_L(K_m\square C_n)=\chi_L(K_m\square P_n).
$$

The conjecture is motivated by the similarity between the structures of $K_m\square C_n$ and $K_m\square P_n$; no resolution is supplied in the source.

## Summary of the result

The conjecture holds with explicit thresholds: for all m ≥ 7 and n ≥ 4 the locating chromatic numbers of K_m □ C_n and K_m □ P_n are equal, both being m + 1 when n ≤ m + 1 and m + 2 otherwise. The path value is Behtoei and Omoomi's own Theorem 2 (re-proved here); the new part is the cycle. Lower bound: each copy of K_m uses m distinct colours, and counting runs of copies that miss the same colour shows that m + 1 colours cannot locate once there are more than m + 1 copies. Upper bounds: for n ≤ m + 1 a cyclic colouring in which each copy misses a different colour, completed by a Hall-type filling; for n ≥ m + 2 two singleton colour classes whose distances separate the copies, with a correction when the cycle is odd. Lean defines the products, graph distance, locating colourings (proper colourings in which the vectors of distances to the colour classes are pairwise distinct) and the locating chromatic number as a least number of colours that is proved to be attained, and proves both formulas and the conjecture.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
