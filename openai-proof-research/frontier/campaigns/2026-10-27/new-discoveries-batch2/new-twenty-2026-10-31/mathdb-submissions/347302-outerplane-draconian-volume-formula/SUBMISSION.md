# MathDB 347302: The Davis–Chen volume formula for adjacency polytopes of outerplane graphs, in the source's form (Conjecture 36, corrected at isolated vertices)

- Problem: https://mathdb.com/p/347302
- Source: Robert Davis and Tianran Chen, “Computing Volumes of Adjacency Polytopes via Draconian Sequences”, arXiv:2007.11051 (2022); Conjecture 36, Eq. (9). https://arxiv.org/abs/2007.11051
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `mathdb347302`, `Dissection.S_nonneg`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Listed as a source-scope result, not in the first group: the MathDB record mis-transcribes the exponent (its formula fails for K₂), and the source's printed Eq. (9) fails for an isolated-vertex block (as does its own proved Corollary 35); what is proved is the corrected source statement. Lean checks the draconian count for every polygon dissection; the normalized-volume formula for all outerplane graphs follows on paper by Davis–Chen's Theorem 8 (which uses Postnikov's results), Proposition 12, Theorem 13 applied to leaf blocks only (its unrestricted printed wording fails for the middle edge of a path on four vertices; the case needed is justified in the paper), and the identification of blocks with polygon dissections. Proof, first (same-model) review and Lean are by Claude Opus 5.5; the cross-model review and final check are by GPT-6.2 Sol (two rounds; the first rejected the literal statement at K₁; the second cleared the corrected statement at not routine 0.80).
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved in the source's form. Davis and Chen (arXiv:2007.11051, Conjecture 36) conjectured a product formula for the normalized volume of the type-PQ adjacency polytope of every outerplane graph, having proved it when every bounded face touches the outer face. The count of draconian sequences that gives the formula is proved for every polygon dissection by a new ear-removal formula; the MathDB record's exponent is mis-transcribed, and the printed formula needs the factor 1 (not 2) for an isolated vertex. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $G$ be an outerplane graph. For each connected component $G_i$ of $G$, let $B_{i,1},\dots,B_{i,b_i}$ be its blocks; let $\mathscr{F}(B_{i,j})$ denote the bounded faces of $B_{i,j}$, let $\operatorname{ewd}{B_{i,j}}$ denote its extended weak dual, and let $v_F$ be the vertex of this dual corresponding to $F$. The normalized volume of the type-PQ adjacency polytope is denoted by $\operatorname{NVol}(\nabla^{\operatorname{PQ}}_G)$. **Outerplane adjacency-polytope volume conjecture.** For any outerplane graph $G$,

$$
\operatorname{NVol}(\nabla^{\operatorname{PQ}}_G) = \prod_{i=1}^k \prod_{j=1}^{b_i} 2^{|V(B_{i,j})| - 2|\mathscr{F}(B_{i,j})|}\prod_{F \in \mathscr{F}(B_{i,j})} \deg_{\operatorname{ewd}{B_{i,j}}}(v_F).
$$

The formula is proved for a proper but large class of outerplane graphs, namely those whose bounded faces are adjacent to the outer face, while experimental data suggests that it holds for all outerplane graphs; a proof remains open.

## Summary of the result

SOURCE-SCOPE RESULT: the formula proved is the one printed in the source (Davis–Chen Eq. (9), exponent 1 + Σ(|F| − 3) per block), not the one in the MathDB record, which mis-transcribes the exponent as |V| − 2|F| and is already false for K₂ and for the square with a chord. With that reading, and with an isolated-vertex block contributing 1 (the printed Eq. (9) and the source's own proved Corollary 35 give 2 there, where the volume is 1), the conjecture holds for every outerplane graph. The new step is an ear formula: removing a minimal ear of a polygon dissection multiplies the number of draconian sequences by an explicit factor with a defect term, and the defect vanishes because the attachment edge is an outer edge of what remains; induction gives the count 2^{1+S}·∏ deg for every polygon dissection, including dissections with inner faces that the source's recurrences (its Theorem 34 and Corollary 35) and Davis–Jakovleski–Pan's triangle recurrence do not reach. Lean proves the draconian count for every polygon dissection on n ≥ 3 vertices. The passage to normalized volumes of all outerplane graphs is on paper: the source's Theorem 8 (via Postnikov), Proposition 12, the leaf-block case of Theorem 13, and the identification of 2-connected outerplane graphs with polygon dissections.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
