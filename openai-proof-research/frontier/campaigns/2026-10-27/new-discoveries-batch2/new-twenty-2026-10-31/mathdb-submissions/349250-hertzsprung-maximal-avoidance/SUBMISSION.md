# MathDB 349250: Bóna's maximal-avoidance conjecture for Hertzsprung patterns

- Problem: https://mathdb.com/p/349250
- Source: Anders Claesson, “From Hertzsprung's problem to pattern-rewriting systems”, arXiv:2012.15309 (2021). (https://arxiv.org/abs/2012.15309)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Hertzsprung.claesson_conj_3_13`, `Hertzsprung.claesson_source`, `Hertzsprung.strict_avoidance`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The 2008 Discrete Mathematics version of Bona's paper is unread (paywalled). One phrase about work associated with Claesson Conjecture 3.14 carries no citation.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. For all k and n and every pattern tau of length k, the number of permutations of n elements avoiding tau in the Hertzsprung sense (consecutive positions and consecutive values) is at most the number avoiding the increasing pattern of length k, with strict inequality when k < n and tau is neither increasing nor decreasing. This settles the maximal-avoidance conjecture of Bona, stated as Conjecture 3.13 by Claesson, including self-overlapping patterns. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $\mathcal{S}_k$ be the set of Hertzsprung patterns of length $k$, let $\tau\in\mathcal{S}_k$, and let $|\mathcal{S}_n(\tau)|$ denote the number of length-$n$ objects avoiding $\tau$. Write $\mathrm{id}_k$ for the identity pattern of length $k$. **Bóna's maximal-avoidance conjecture.** For every Hertzsprung pattern $\tau\in\mathcal{S}_k$ and every natural number $n$,

$$
|\mathcal{S}_n(\tau)|\leq |\mathcal{S}_n(\mathrm{id}_k)|.
$$

Bóna proved the inequality for non-self-overlapping patterns. The paper reports computational evidence suggesting that self-overlapping patterns also satisfy it, but gives no general proof.

## Summary of the result

For all k and n and every pattern tau in S_k, the number of permutations of [n] with no Hertzsprung occurrence of tau (consecutive positions, values order-isomorphic with a single shift) is at most the number with no Hertzsprung occurrence of the identity pattern of length k; the inequality is strict when k < n and tau is neither the identity nor its reverse. This is the maximal-avoidance conjecture of Bona as stated in Claesson Conjecture 3.13, including the self-overlapping patterns that the earlier argument did not cover. The proof compares first and second moments of occurrence counts.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
