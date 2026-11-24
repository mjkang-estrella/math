# MathDB 372803: The minimum-fort-size conjecture for marginal observances

- Problem: https://mathdb.com/p/372803
- Source: Beth Bjorkman, Sean English and Johnathan Koch, “Cost-Benefit Analysis for PMU Placement in Power Grids”, arXiv:2601.19775 (2026). (https://arxiv.org/abs/2601.19775), Conjecture 4.1
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `FortObservance.minimumFort_marginalObs_refuted`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. No claim that 25 vertices is the smallest counterexample. Lean proves the power domination number is at least 3 (the exact value 4 is the referee's computation). The source is a 2026 arXiv preprint with no citing papers yet. The prior-work paragraph of the paper still refers to internal review files and should be tidied before external use.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted. A 25-vertex graph built from two Fano-plane gadgets and a hub has minimum fort size 4, yet its second marginal observance is 3 (maximum observances 11 and 14 with one and two sensors; power domination number at least 3). This contradicts Conjecture 4.1 of Bjorkman, English and Koch, arXiv:2601.19775. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $G$ be a graph. Write $\underline{f}(G)$ for the minimum fort size of $G$, let $\mathrm{MObs}(G;i)$ denote the marginal observance at step $i$, and let $\gamma_P(G)$ denote the power domination number. For a positive integer $k$, write $[k]=\{1,\ldots,k\}$. **Minimum-fort-size conjecture.** If

$$
\underline{f}(G)\geq 4,
$$

then

$$
\mathrm{MObs}(G;i)\geq 4
$$

for all $i\in[\gamma_P(G)]$. This asks whether the relationship between minimum fort size and marginal observances established for smaller minimum fort sizes extends to minimum fort size at least four; its status is not resolved in the source.

## Summary of the result

The conjecture that minimum fort size at least 4 forces every marginal observance MObs(G;i), for i up to the power domination number, to be at least 4 is false. An explicit graph on 25 vertices, built from two copies of the Fano plane with two lines removed joined through a hub, has no fort of size at most 3, maximum observed-set sizes 11 and 14 with one and two sensors, and power domination number at least 3, so its second marginal observance is 3. (By the referee's computation the maximum observances are 0, 11, 14, 19, 25 and the power domination number is 4.) A generic random search over about 80 million graphs on 10 to 28 vertices found no counterexample; the witness comes from a structured construction.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
