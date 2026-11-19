# MathDB 382145: Dickenstein–Nill Cayley decomposition conjecture for lattice polytopes

- Problem: https://mathdb.com/p/382145
- Source: Sofía Garzón Mora and Christian Haase, “Fine Polyhedral Adjunction Theory”, arXiv:2302.04074 (2023). (https://arxiv.org/abs/2302.04074)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoint `Cayley382145.dickensteinNillCayleyConjecture_holds`; axioms limited to propext, Classical.choice, Quot.sound; independently extracted and replayed from `LEAN-SOURCE-APPENDIX.md`.
- Written proof: `PAPER.md` (independently reviewed, no theorem-affecting gaps).
- Novelty: bounded literature and registry review only; no worldwide-priority claim. User may overrule. Garzon Mora FU Berlin dissertation unread; withdraw if it proves the conjecture.
- Produced with AI assistance (GPT-6.2 Sol and Claude Opus 5.5 investigators, independent AI review); not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the Dickenstein-Nill Cayley decomposition conjecture, as reformulated by Di Rocco, Haase, Nill and Paffenholz. Every n-dimensional lattice polytope whose Q-codegree mu exceeds (n+1)/2 is a Cayley sum of lattice polytopes of dimension at most the floor of 2(n+1-mu); the direct proof uses an optimal dual certificate of minimal support and its heavy facets, independently of the earlier theorem in the literature. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $P$ be an $n$-dimensional lattice polytope, and let $cmu(P)$ denote its $cmathbb{Q}$-codegree. A **Cayley sum** is a polytope constructed by placing polytopes along the vertices of a standard simplex and taking their convex hull.

**Dickenstein–Nill's Cayley decomposition conjecture.** If

$$
\mu(P) > \frac{n+1}{2},
$$

then $P$ decomposes as a Cayley sum of lattice polytopes of dimension at most

$$
\left\lfloor 2(n+1-\mu(P)) \right\rfloor.
$$

The stronger conjecture by Dickenstein and Nill was disproved by Higashitani; the weaker version recorded here remains open. A slightly weaker statement, with the hypothesis $\mu(P) \geq \frac{n+2}{2}$, is known.

## Summary of the result

MODEST_BOUNDED (close call): direct heavy-slack projection proof of the Q-codegree Cayley decomposition conjecture, independent of DRHNP Theorem 3.4; the strongest objection is that Theorem 3.4 leaves only the even-dimensional width-one case, which is elementary.

The complete proof is in `PAPER.md`; the complete Lean source is in `LEAN-SOURCE-APPENDIX.md`.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
