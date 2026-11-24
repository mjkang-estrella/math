# MathDB 350694: Vertex-cut obstruction for betweenness-uniform blow-ups

- Problem: https://mathdb.com/p/350694
- Source: David Hartman and Aneta Pokorná, “Constructions of betweenness-uniform graphs from trees”, arXiv:2105.06777 (2021; EuroComb 2021), Conjecture 12. https://arxiv.org/abs/2105.06777
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `BlowupBetweenness.hartman_pokorna_conj12_false`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Close call on routine (cross-model reviewer and final checker both about 0.60 not routine): disjoint-clique parts are published (Gago, Coroničová Hurajová and Madaras 2013), and what is new is using the non-adjacent pairs of such a part at the cut vertex as a free balancing parameter. The witness has a disconnected part at the cut vertex, which the source allows (it uses edgeless parts itself); the variant with connected parts is open. The construction came from a GPT-6.1 Sol proof lane (3176-vertex family, also formalized), the smaller 1061-vertex witness from the Claude Opus pre-Lean review, and the Lean from a Claude Opus lane; the final check was by a separate Opus lane (same model family as the packager) because GPT-6.1 Sol hit its usage limit.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted. Hartman and Pokorná conjectured (arXiv:2105.06777, Conjecture 12) that no blow-up of a graph with diameter at least 3 and a cut vertex is betweenness-uniform. A blow-up of the wedge of two 5-cycles on 1061 vertices, with a disjoint union of cliques at the cut vertex, has every betweenness equal to 100. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $G$ be a graph of order $n$ with diameter at least three and having a vertex cut of size one. For graphs $H_1,\dots,H_n$, let $G[H_1,\dots,H_n]$ be the corresponding blow-up of $G$. **Vertex-cut obstruction.** There are no graphs $H_1,\dots,H_n$ such that $G[H_1,\dots,H_n]$ is betweenness-uniform.

## Summary of the result

The conjecture is false. Let G be the wedge of two 5-cycles (order 9, diameter 4, the common vertex a cut vertex). Replace the four neighbours of the cut vertex by K100, the four remaining vertices by K5, and the cut vertex by K604 ⊔ K8 ⊔ K4 ⊔ 25·K1. The resulting 1061-vertex blow-up is connected and every vertex has betweenness exactly 100. The source's obstruction for trees comes from leaves, whose parts carry no global load; in the two-C5 wedge every part lies on a cycle, and a part of the cut vertex that is a disjoint union of cliques adds load only to the neighbouring parts, so its number of non-adjacent pairs is a free parameter that balances the equations. The proof is a general formula for the betweenness of a blow-up whose parts are disjoint unions of cliques, from a lifting lemma for shortest paths; Lean proves the formula in general and evaluates it on the 9-vertex base, never enumerating the 1061 vertices. Lean's betweenness is the source's (unordered pairs), shared verbatim with the accepted 382260 packet.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
