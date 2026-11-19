# MathDB 366258: Treewidth-connectivity partition conjecture for graphs

- Problem: https://mathdb.com/p/366258
- Source: Stijn Cambie, François Dross, Kolja Knauer, Hoang La and Petru Valicov, “Partitions of planar (oriented) graphs into a connected acyclic and an independent set”, arXiv:2412.11774 (2025). (https://arxiv.org/abs/2412.11774)
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoint `MathDB366258.native_refutation`; axioms limited to propext, Classical.choice, Quot.sound; independently extracted and replayed from `LEAN-SOURCE-APPENDIX.md`.
- Written proof: `PAPER.md` (independently reviewed, no theorem-affecting gaps).
- Novelty: bounded literature and registry review only; no worldwide-priority claim. EJC final scope unread.
- Produced with AI assistance (GPT-6.2 Sol and Claude Opus 5.5 investigators, independent AI review); not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the treewidth-connectivity partition conjecture, Conjecture 36 of Cambie, Dross, Knauer, La and Valicov, at k = 3. A 16-vertex, 34-edge graph has treewidth 3 and vertex connectivity 3, yet for every independent vertex set the remaining induced subgraph has treewidth at least 3 or becomes disconnected after deleting at most one vertex; an ordinary argument extends the failure to every k >= 3. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $G$ be a graph, and let $k$ be an integer such that $G$ has treewidth at most $k$ and connectivity at least $k$. A vertex set inducing a graph of treewidth at most $k-1$ and connectivity at least $k-1$ is denoted by $\mathcal{T}$, and an independent set is denoted by $\mathcal{I}$. **Treewidth-connectivity partition conjecture.** The vertices of $G$ can be partitioned into an induced graph $\mathcal{T}$ of treewidth at most $k-1$ and connectivity at least $k-1$, and an independent set $\mathcal{I}$. This is proposed as a generalization of a theorem for graphs of treewidth at most $2$; the source leaves it as a belief rather than an established result.

## Summary of the result

SUBSTANTIVE_BOUNDED: 16-vertex 34-edge graph of treewidth 3 and connectivity 3 with no admissible partition; extension to all k>=3 is ordinary only.

The complete proof is in `PAPER.md`; the complete Lean source is in `LEAN-SOURCE-APPENDIX.md`.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
