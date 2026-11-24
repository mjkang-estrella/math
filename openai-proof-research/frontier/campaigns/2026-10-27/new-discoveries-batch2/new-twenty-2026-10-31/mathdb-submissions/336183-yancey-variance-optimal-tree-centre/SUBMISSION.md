# MathDB 336183: Variance-optimal functions on trees are centered at a vertex

- Problem: https://mathdb.com/p/336183
- Source: Matthew Yancey, “Probabilistic and Geometrical Applications to Graph Theory”, arXiv:1705.09725 (2017). (https://arxiv.org/abs/1705.09725), Conjecture 1.4
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Yancey.mathdb336183`, `Yancey.counterexample`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Bounded literature and registry search only; no erratum or later paper on Lemma 19 of Farhadi-Louis-Singh-Tetali was found. The statement that every tree with at most 18 vertices satisfies the conjecture is an unpublished computation by the referee and is not kernel-checked. No claim that 34 vertices is minimal.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted. On an explicit tree with 34 vertices, a feasible function has score 14892 while every function centred at a vertex has score at most 14888, so no variance-optimal function on this tree is centred at a vertex; this contradicts Yancey's Conjecture 1.4. The same example shows that the proof of Lemma 19 of Farhadi, Louis, Singh and Tetali (arXiv:2003.05582), which asserts the centred form, is incomplete at its sign-choice step. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $T$ be a tree and let $X$ be a variance-optimal function over $T$. For vertices $u,r\in V(T)$, write $d(u,r)$ for their graph distance.

**Tree characterization conjecture.** There exists a vertex $r$ such that, for every vertex $u\in V(T)$,

$$
|X(u)-X(r)|=d(u,r).
$$

Moreover, if $T$ is not a path, then $r$ may be chosen so that $d(r)\geq 3$.

The conjecture is proposed as a simple characterization of variance-optimal functions on trees and as a strengthening of the preceding structural result about hairs. The supplied text gives no resolution.

## Summary of the result

Conjecture 1.4 of Yancey (every variance-optimal function on a tree is centred at a vertex r, with |X(u) - X(r)| = d(u, r) for all u, and r of degree at least 3 when the tree is not a path) is false. On an explicit tree with 34 vertices a feasible function has score 14892, while every vertex-centred function has score at most 14888 (the best centres are vertices 0, 2 and 7), so no variance-optimal function on this tree has a centre. Lean proves that an optimal function exists on the witness and that the first clause fails for every optimum, hence the negation of the whole conjecture. The result contradicts Lemma 19 of Farhadi, Louis, Singh and Tetali (arXiv:2003.05582v3), whose proof treats three sign choices as independent; on the witness the three moves change the variance by -1/289, -72/289 and -1/289 rather than giving the claimed gain of 71/289. Every tree with at most 18 vertices satisfies the conjecture (referee's unpublished computation).

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
