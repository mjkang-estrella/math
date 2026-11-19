# MathDB 374966: Lattice-realization conjecture for preorder lattice-point posets

- Problem: https://mathdb.com/p/374966
- Source: Frédéric Chapoton and Christos A. Athanasiadis, “Polytopes and posets associated to preorders”, arXiv:2605.26916 (2026). (https://arxiv.org/abs/2605.26916)
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoint `A374966.conj81_false_at_corolla_native`; axioms limited to propext, Classical.choice, Quot.sound; independently extracted and replayed from `LEAN-SOURCE-APPENDIX.md`.
- Written proof: `PAPER.md` (independently reviewed, no theorem-affecting gaps).
- Novelty: bounded literature and registry review only; no worldwide-priority claim. All-corolla extension is ordinary only; Lean covers t3.
- Produced with AI assistance (GPT-6.2 Sol and Claude Opus 5.5 investigators, independent AI review); not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the lattice-realization conjecture of Athanasiadis and Chapoton, that every preorder's lattice-point poset is realized by a finite graded lattice with matching zeta and M-triangle data. It already fails for the three-element corolla, one maximum over two incomparable minima: the M-triangle equation alone has no solution, its diagonal forcing five elements in each of ranks 1 and 2 while further coefficients overcount the available pairs. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $\tau$ be a preorder of size $n$, let $P_\tau$ be its lattice-point poset, let $M_{P_\tau}(x,y)$ be its $M$-triangle, and let $\overline{M}_{P_\tau}$ be the transmutation defined by

$$
\overline f(x,y)=f\left(\frac{1-y}{1-xy},1-xy\right).
$$

**Lattice-realization conjecture.** There exists a finite graded lattice $L_\tau$ of rank $n$ such that

$$
\mathcal Z(P_\tau,t)=\mathcal Z(L_\tau,t),\qquad \overline M_{P_\tau}(x,y)=M_{L_\tau}(x,y).
$$

In particular, the rank-generating polynomial of $L_\tau$ equals $h(\tau,t)$. The conjecture extends the arbor setting; the source gives examples for chain preorders but no general resolution.

## Summary of the result

SUBSTANTIVE_MODEST: Conjecture 8.1 fails at the three-element corolla by a cover-incidence double count (13 required, at most 10 possible); contradicts the computational expectation in Chapoton section 9.

The complete proof is in `PAPER.md`; the complete Lean source is in `LEAN-SOURCE-APPENDIX.md`.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
