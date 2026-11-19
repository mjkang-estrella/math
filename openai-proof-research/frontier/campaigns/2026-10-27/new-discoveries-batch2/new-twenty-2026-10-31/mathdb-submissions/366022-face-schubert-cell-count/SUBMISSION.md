# MathDB 366022: Cell-count conjecture for face Schubert arrangements of polytopes

- Problem: https://mathdb.com/p/366022
- Source: Sebastian Seemann and Francesca Zaffalon, “How to stab a polytope”, arXiv:2412.00551 (2024). (https://arxiv.org/abs/2412.00551)
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoint `G366022.mathdb_366022_counterexample`; axioms limited to propext, Classical.choice, Quot.sound; independently extracted and replayed from `LEAN-SOURCE-APPENDIX.md`.
- Written proof: `PAPER.md` (independently reviewed, no theorem-affecting gaps).
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Pavlov-Ranestad journal final unread.
- Produced with AI assistance (GPT-6.2 Sol and Claude Opus 5.5 investigators, independent AI review); not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the cell-count conjecture of Seemann and Zaffalon for face Schubert arrangements of polytopes, Conjecture 3.5. An eight-vertex rational polytope in projective 3-space has two lines meeting its interior and avoiding the span of every edge that carry the same strict sign vector yet lie in different connected components of the stabbing complement, so the components outnumber the realized sign vectors. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $P\subseteq \mathbb{P}^{n-1}$ be a full-dimensional polytope, and let $P^{[k]}$ denote its $k$-stabbing set. Consider the $k$-face Schubert arrangement of $P$ inside $P^{[k]}$, and the sign vectors determined by its defining equations for $V\in P^{[k]}\setminus \mathcal{H}_P^k$. **Cell-count conjecture.** The number of cells in this arrangement is equal to the number of sign vectors realized by such spaces $V$. This would show that, for Schubert arrangements arising from polytopes, cells are uniquely determined by their realized sign vectors; the claim is presented as an expectation, and no resolution is supplied in the source.

## Summary of the result

SUBSTANTIVE_BOUNDED: eight-vertex rational polytope with two stabbing lines sharing a strict sign vector in different components; convex realization not in inspected prior. Component finiteness is ordinary, the count inequality is kernel-checked.

The complete proof is in `PAPER.md`; the complete Lean source is in `LEAN-SOURCE-APPENDIX.md`.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
