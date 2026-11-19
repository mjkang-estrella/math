# MathDB 355218: Line-middle graph inequality conjecture for outer-connected domination

- Problem: https://mathdb.com/p/355218
- Source: Farshad Kazemnejad, Behnaz Pahlavsay, Elisa Palezzato and Michele Torielli, “Connected and outer-connected domination number of middle graphs”, arXiv:2206.15439 (2022). (https://arxiv.org/abs/2206.15439)
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `OuterDom.mathdb_355218`, `OuterDom.mathdb_355218_nonempty`, `OuterDom.CliquePath.clique_path_strict`, `OuterDom.CliquePath.infinitely_many_counterexample_orders`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Low significance, and a second credit from the same source section as 355217 (user may overrule). Lean proves bounds sufficient for the refutation; exact values are in the written proof only.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted. For every h >= 2, take two copies of the complete graph K_{2h} joined by a path with three edges. The outer-connected domination number of its middle graph is 2h+2, while that of its line graph is C(2h,2)+h+1 (6 against 9 at h = 2), so the conjectured inequality that the line graph value is at most the middle graph value fails for infinitely many connected graphs, under either convention for an empty complement. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $G$ be a graph of order $n\ge 2$, and let $L(G)$ and $M(G)$ denote its line graph and middle graph, respectively. The **line-middle graph inequality conjecture** asserts that

$$
\gamma{\tilde{}} _{c}(L(G)) \le \gamma{\tilde{}} _{c}(M(G)).
$$

The inequality is supported by the preceding results, including strict inequality for wheels of order at least five; equality occurs for at least one connected graph of order four. A classification of graphs for which equality holds is posed separately as an open problem, while the general inequality remains open.

## Summary of the result

Conjecture 7.6 of the source (the outer-connected domination number of the line graph is at most that of the middle graph) is false: for every h >= 2 the graph formed by two copies of K_{2h} joined by a three-edge path has outer-connected domination number 2h+2 for its middle graph and C(2h,2)+h+1 for its line graph (6 against 9 at h = 2), under both conventions for an empty complement. Lean proves explicit bounds giving the strict inequality for every h and infinitely many counterexample orders; the exact values are proved in the paper. Significance is low; this is a second result from section 7 of the same source as accepted 355217.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
