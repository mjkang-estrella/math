# MathDB 343652: Strong-product immersion conjecture

- Problem: https://mathdb.com/p/343652
- Source: Karen L. Collins, Megan E. Heenehan and Jessica McDonald, “Clique immersion in graph products”, arXiv:1908.10457 (2019). https://arxiv.org/abs/1908.10457
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `ProductImmersion.strong_product_conjecture_false`, `ProductImmersion.literal_immersion_number_counterexample`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Close to recent work: Wu and Deng, arXiv:2605.28518, refuted the sibling conjecture for the direct product and left the strong product open; their parity argument does not transfer, and the new step here is the compression of matchings into shared vertices, which both reviewers call a modest but real structural change (cross-model confidence: refutation correct 0.97, not routine 0.6, overall 0.75). Wu and Deng's 2025 note on strong products could not be read (the site refuses automated clients); its published hypotheses do not cover these factors. The Lean immersion number is defined with a cap at the number of vertices, justified by a proved bound. The packet disables one compiler linter for the unchanged sources; root confirmed the axioms and the absence of placeholder proofs. The wrapper module with the negated universal statement was read by the GPT-6.1 Sol final check only.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted. For G = F_4 (14 vertices, immersion number 8) and H = F_6 (22 vertices, immersion number 12), where F_a is K_{a,a} with one extra vertex per perfect matching on each side, the strong product G ⊠ H has immersion number less than 96. So the immersion number is not supermultiplicative for the strong product. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $G$ and $H$ be graphs, and write $\operatorname{im}(G)=t$ and $\operatorname{im}(H)=r$. **Strong-product immersion conjecture.** Then

$$
\operatorname{im}(G\boxtimes H)\geq tr.
$$
 This conjecture is motivated by the identity $K_t\boxtimes K_r=K_{tr}$ and the resulting immersion number of the strong product of complete graphs; the paper presents it as an unresolved conjecture.

## Summary of the result

The conjecture that the immersion number is supermultiplicative for the strong product, im(G) im(H) <= im(G ⊠ H), is false. Let F_a be the complete bipartite graph K_{a,a} with, on each side, one extra vertex shared by each perfect matching (a compressed form of adding a matching). With G = F_4 on 14 vertices and H = F_6 on 22 vertices, im(G) = 8 and im(H) = 12, but K_96 does not immerse in the 308-vertex product G ⊠ H: only 96 vertices of the product have degree at least 95, so they would have to be the branch vertices, and a checkerboard cut separating them 48 against 48 has 2,224 edges while 48 * 48 = 2,304 edge-disjoint paths would have to cross it. Lean defines weak immersions, the immersion number and the strong product, proves the two immersion numbers, the degree and cut counts, and derives the negation of the universal statement.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
