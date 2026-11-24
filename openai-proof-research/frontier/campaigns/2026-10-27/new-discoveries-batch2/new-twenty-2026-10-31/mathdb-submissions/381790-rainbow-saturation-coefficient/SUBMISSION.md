# MathDB 381790: Exact formula conjecture for the rainbow-saturation coefficient

- Problem: https://mathdb.com/p/381790
- Source: Debsoumya Chakraborti, Kevin Hendrey, Ben Lund and Casey Tompkins, “Rainbow saturation for complete graphs”, arXiv:2212.04640 (2022; v2 2024; SIAM J. Discrete Math.), Conjecture 5.1. https://arxiv.org/abs/2212.04640
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Rainbow381790.chlt_conj_5_1_false`, `Rainbow381790.f_514_lt_conjFormula`, `Rainbow381790.f_family_le`, `Rainbow381790.f_le_all_k`, `Rainbow381790.conj_fails_on_family`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The construction is one page and elementary once seen (cross-model reviewer: not routine 0.80; final checker 0.75-0.80). The Lean definition of f fixes the palette to ℕ: a first formalization with an arbitrary palette type was vacuous (the empty palette admits the zero-vertex graph, so f = 0), found and proved by the Lean lane; root fixed the palette to ℕ, which the source states and which gives the same f as any infinite palette. The Θ(r^{1/3}) statement uses the source's Lemma 3.10 for its lower half, quoted, not formalized. The SIAM journal text was not read (403). The Lean was written by GPT-6.1 Sol lanes and finished by a Claude Opus 5.5 lane; because GPT-6.1 Sol hit its usage limit, the final check was by a separate Claude Opus 5.5 lane, the same model family as the packager (the cross-model review is the Opus pre-Lean review of a Sol proof).
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted. Chakraborti, Hendrey, Lund and Tompkins conjectured (arXiv:2212.04640, Conjecture 5.1) that the rainbow-saturation coefficient α_{k+2} equals f(k) = k + ⌈(−1 + √(4k−3))/2⌉. A tripartite construction gives f(514) ≤ 536 < 537, and in general f(k) ≤ k + 3⌈(k−2)^{1/3}⌉, so α_r − r grows like r^{1/3}, not √r. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

For each integer $k\geq 4$, let $f(k)$ be the auxiliary extremal function from the paper and let $\alpha_{k+2}$ be the coefficient in the asymptotic formula for rainbow saturation, so that $\operatorname{sat}(n,\mathcal{R}(K_{k+2}))=\alpha_{k+2}n+O(1)$. **Exact coefficient conjecture.** For every $k\geq 4$, $$\alpha_{k+2}=f(k)=k+\left\lceil\frac{-1+\sqrt{4k-3}}{2}\right\rceil.$$

## Summary of the result

The conjectured formula fails: f(514) ≤ 536 < 537. Take three parts A, B, C of t vertices with every edge between different parts and none inside a part; add one private vertex for each triangle abc, put all private vertices in a clique joined to everything else, and give the edge ab and the edges from each c to its private vertex for (a, b, c) one shared colour, every other edge its own colour. A clique uses at most one vertex of C, so it meets each shared colour at most once, except the full triangle with its own private vertex; this gives a member of the source's class with t³ + 3t vertices for k = t³ + 2, which beats the formula from t = 8 on. A variable-core version gives f(k) ≤ k + 3⌈(k−2)^{1/3}⌉ for every k ≥ 4. Since the source's Lemma 3.3 proves α_{k+2} = f(k), the printed chain is false; together with the source's lower bound (its Lemma 3.10, quoted and not formalized), α_r − r = Θ(r^{1/3}), against the square-root growth the formula predicts. Lean states the source's three properties literally with colours in ℕ (the source's own palette), proves the refutation, the t-family, the every-k bound and that the formula fails for every t ≥ 8, and checks that f(k) ≥ k + 1 for k ≥ 1 and that the rainbow K_{k+1} is not a member.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
