# MathDB 331692: Extremal maximal-matchings conjecture for benzenoid chains

- Problem: https://mathdb.com/p/331692
- Source: Tomislav Došlić and Taylor Short, “Maximal matchings in polyspiro and benzenoid chains”, arXiv:1511.00590 (2015); Appl. Anal. Discrete Math. 15 (2021) 179-200, Conjecture 5.19. (https://arxiv.org/abs/1511.00590)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Helicene.MathDB331692`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The kernel-checked endpoint is stated for graphs with a hexagon-chain witness; the passage from the source's plane-graph definition to the witness (and back) is prose, not Lean, since Mathlib has no plane embeddings. An independent referee judged that bridge sound and complete. No uniqueness claim (the helicene ties with the zigzag chain at n = 4). Chen and Zhang (Filomat 2025) still list the problem as open.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Among benzenoid chains of each length the helicene has the minimum number of maximal matchings (Conjecture 5.19 of Došlić and Short). The proof uses a nine-state transfer matrix and five certified terminal replacements. Lean verifies the statement for all graphs with an explicit hexagon-chain structure; the step from the plane-graph definition of a benzenoid chain to that structure is proved in the paper in prose. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $B_n$ be a benzenoid chain of length $n$, and let $H_n$ denote the helicene benzenoid chain of length $n$. For a graph $G$, write $Psi(G)$ for its number of maximal matchings.

**Extremal maximal-matchings conjecture.** For every benzenoid chain $B_n$ of length $n$,

$$
\Psi(H_n) \leq \Psi(B_n).
$$

The conjecture asserts that the helicene has the smallest number of maximal matchings among all benzenoid chains of the same length. The surrounding discussion presents this as an unresolved extremal problem and notes that maximal matchings appear to decrease as the number of kinky hexagons increases, while their value may also depend on the direction of successive turns.

## Summary of the result

Among benzenoid chains with n hexagons, the helicene has the fewest maximal matchings. Lean proves: for every finite simple graph G carrying a hexagon-chain witness of length n (an ordered list of n six-cycles covering all vertices and edges, consecutive ones sharing exactly one edge, non-consecutive ones disjoint, the two shared edges of an interior hexagon disjoint), the number of inclusion-maximal matchings of the explicit helicene graph with n hexagons is at most that of G. The equivalence between the source's definition (a plane graph whose bounded faces are hexagons arranged in a chain) and the existence of such a witness, and the identification of the Lean helicene with the source's helicene, are proved in the paper in prose, because Mathlib has no plane embeddings. The minimizer is not unique at n = 4 (the zigzag chain ties at 288); for n = 5 to 10 the helicene and its mirror image are the only minimizers (referee's enumeration of 9,841 chains).

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
