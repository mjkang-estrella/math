# MathDB 361098: Odd-order graphs do not exhibit Laplacian perfect state transfer

- Problem: https://mathdb.com/p/361098
- Source: Steve Kirkland and Hermie Monterde, “Quantum walks on join graphs”, arXiv:2312.06906 (2023). https://arxiv.org/abs/2312.06906
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Pool012.odd_order_laplacian_pst_refuted`, `Pool012.source_conjecture77_refuted`, `Pool012.source_explicit_counterexample`, `Pool012.witness_exact_transfer`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Bounded literature search only; the journal text of the source is unread. Lean checks only the 35-vertex member; the infinite family is proved on paper. Whether a smaller counterexample exists is not known: a reviewer's exhaustive search found none among all graphs of odd order up to 9 (34.2 million at order 9), and none of the twin-based three-cell type up to order 23; that search is a computation, not part of the Lean proof. The construction uses the published twin criterion of Kirkland, Monterde and Plosker, and a specialist might call twins plus a quotient matrix plus a parameter choice standard technique (cross-model confidence: correct 0.99, not public 0.9, first tier rather than second 0.75). The packet raises Lean's memory threshold option for the 35-vertex computation; no check is weakened. The cross-model reviewer read the four core modules before packaging (they are byte-identical in the packet); the added 62-line module in the source's vocabulary was checked by the GPT-6.1 Sol final check only.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted. A connected simple graph on 35 vertices (two twins joined to 22 vertices, which are joined biregularly to 11 more) has Laplacian perfect state transfer at time pi/2, contradicting the odd-order conjecture of Kirkland and Monterde (arXiv:2312.06906). It is the first member of an infinite family of orders 36k^2 - 1. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $X$ be a simple connected unweighted graph on an odd number of vertices. **Odd-order Laplacian PST conjecture.** Laplacian perfect state transfer does not occur in $X$. This extends the corresponding result for unweighted graphs on $3$ or $5$ vertices and follows for weighted join graphs under the additional assumption that the characteristic polynomial of the Laplacian has integer coefficients; the general case remains open.

## Summary of the result

The conjecture of Kirkland and Monterde that Laplacian perfect state transfer does not occur in a simple connected unweighted graph of odd order is false. An explicit connected graph on 35 vertices has perfect state transfer between two vertices at time pi/2: two nonadjacent twin vertices u, v are joined to every vertex of a set W of 22 vertices, each vertex of W has 8 neighbours in a set R of 11 vertices, and each vertex of R has 16 neighbours in W. The Laplacian eigenvalues on the symmetric vector e_u + e_v are 0, 20 and 28, all divisible by 4, and the eigenvalue on e_u - e_v is 22, congruent to 2 modulo 4, so exp(i pi L / 2) maps e_u to e_v. The graph is the case k = 1 of a family of orders 36k^2 - 1 (r = 12k^2 - 1, c = 8k^2), proved on paper for all k. Lean checks the 35-vertex graph: it defines the conjecture for all simple connected graphs on an odd number of vertices with Mathlib's Laplacian and the complex matrix exponential, proves connectedness and the eigenvector identities by kernel computation, and derives the negation.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
