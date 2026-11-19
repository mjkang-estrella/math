# MathDB 364626: Finiteness conjecture for connected graphs with odd metamour period

- Problem: https://mathdb.com/p/364626
- Source: William Q. Erickson, Daniel Herden, Jonathan Meddaugh, Mark R. Sepanski, Mitchell Minyard and Kyle Rosengartner, “Limits and Periodicity of Metamour 2-Distance Graphs”, arXiv:2409.02306 (2024). (https://arxiv.org/abs/2409.02306)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoint `Metamour.Review.finite_native_least_labeled_odd_return`; axioms limited to propext, Classical.choice, Quot.sound; independently extracted and replayed from `LEAN-SOURCE-APPENDIX.md`.
- Written proof: `PAPER.md` (independently reviewed, no theorem-affecting gaps).
- Novelty: bounded literature and registry review only; no worldwide-priority claim. FAU abstract body, Leonor thesis and several primary bodies unread.
- Produced with AI assistance (GPT-6.2 Sol and Claude Opus 5.5 investigators, independent AI review); not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the finiteness conjecture for connected graphs of odd metamour period. If k is odd and the k-th iterate of the distance-two metamour operation returns a finite connected graph to itself, then explicit bounds in k limit the maximum degree, the diameter and hence the order, so only finitely many isomorphism classes have exact odd period k; this answers Conjecture 7.7 of Erickson, Herden, Meddaugh, Sepanski, Minyard and Rosengartner. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

A graph's **metamour period** is the least positive integer $k$ for which its iterated metamour graph returns to the original graph, under the metamour operation used in the paper. Let $k$ range over the positive odd integers.

**Finiteness conjecture.** For each odd $k\in \mathbb{Z}^+$, there exist only finitely many connected graphs with metamour period $k$.

The paper has already classified the connected graphs with metamour period $3$: they are $C_7$ and $C_9$. The conjecture predicts analogous finiteness for every odd period, and the classification of such graphs remains open in general.

## Summary of the result

SUBSTANTIVE_BOUNDED: explicit order bound at each odd metamour period via a temporal-word triangle obstruction and Ramsey degree bound; no complete bridge in inspected bodies.

The complete proof is in `PAPER.md`; the complete Lean source is in `LEAN-SOURCE-APPENDIX.md`.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
