# MathDB 337947: Solid k-minor essentiality conjecture

- Problem: https://mathdb.com/p/337947
- Source: Anna Brosowsky, Sunita Chepuri and Alex Mason, “Parametrizations of k-Nonnegative Matrices: Cluster Algebras and k-Positivity Tests”, arXiv:1712.05037 (v3 2021; J. Combin. Theory Ser. A 2020), Conjecture 4.6; first stated in a 2017 REU report. https://arxiv.org/abs/1712.05037
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `KEss.solid_minors_k_essential`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. A short, clean note on classical total-positivity tools (Karlin-style kernels, divided differences, discrete B-spline positivity); the new part is the combination of two opposite perturbations (cross-model reviewer: not routine 0.65; final checker about 0.6). Wording: the MathDB record paraphrases k-essential as 'necessary in a k-positivity test'; the result concerns tests made of minors, not tests that may use non-minors. The publisher's version was not read (arXiv v3, posted after the journal version, still states the conjecture). The Lean was written by a Claude Opus 5.5 lane from a GPT-6.1 Sol proof; the final check was by a separate Opus lane (same model family as the packager) because GPT-6.1 Sol hit its usage limit; a Sol re-check after 2026-11-26 is advisable.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Brosowsky, Chepuri and Mason's Conjecture 4.6 (arXiv:1712.05037): every solid k-minor is k-essential, i.e. for each one some matrix makes it nonpositive while all other minors of order at most k are positive. The source had k ≤ 3; the new construction uses a polynomial kernel with two opposite discrete-spline perturbations. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let a **solid $k$-minor** be a $k\times k$ minor using consecutive rows and consecutive columns, and call a minor **$k$-essential** if some matrix has that minor nonpositive and every other minor of order at most $k$ positive. **Solid-minor essentiality conjecture.** Solid $k$-minors are $k$-essential.

## Summary of the result

For every n, every 1 ≤ k ≤ n and every solid position, there is an n×n matrix (rational for rational t) whose distinguished solid k-minor is 0 while every other minor of order at most k is positive, so every k-positivity test made only of minors must contain all solid k-minors. The source proved k ≤ 3 with ε-power constructions around a 0/1 central block and noted that its method fails beyond k = 3. The new construction perturbs a weighted rank-(k−1) polynomial moment kernel by two opposite rank-one terms built from a discrete binomial spline with exactly one zero divided difference; with two opposite perturbations the leading term of every other minor is a sum of two nonnegative quantities, at least one positive (one perturbation provably fails). Lean states minors over sorted index sets and k-essential as in the source, and proves the statement for every n, k and position by a general argument (a function-sum expansion in place of Cauchy–Binet, which the pinned Mathlib lacks; Lagrange divided differences; a continuity argument for the common parameter).

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
