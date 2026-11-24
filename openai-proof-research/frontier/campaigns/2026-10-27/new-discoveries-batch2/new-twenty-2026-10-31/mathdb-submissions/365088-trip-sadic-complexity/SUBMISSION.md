# MathDB 365088: The complexity bound conjecture for S(e,23,e)-adic languages

- Problem: https://mathdb.com/p/365088
- Source: Thomas Garrity and Otto Vaughn Osterman, “On the Factor Complexity Associated with a Family of Multidimensional Continued Fraction Algorithms”, arXiv:2410.02032 (2026; Combinatorics and Number Theory 15:4, 2026), Conjecture 53. https://arxiv.org/abs/2410.02032
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `garrity_osterman_conj53`, `garrity_osterman_conj53_prop`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The conjecture's surrounding text mentions twins and conjugates of S(e,23,e); those transfer by the source's proved Propositions 45 and 47 (the final check verified directly that each of the 5 conjugates and 6 twins in the source's appendix is a letter-permuted or reversed copy) and are not formalized. A specialist would see the result as the authors' announced strategy carried to completion, with one new ingredient (the cross-age matching); cross-model reviewer: not routine 0.55, at the floor root uses for counting; the final checker judged it a real step and asked for modest wording. The Lean was started by a GPT-6.1 Sol lane and finished by a Claude Opus 5.5 lane (4,097 lines in 23 modules); because GPT-6.1 Sol hit its usage limit, the final check was by a separate Claude Opus 5.5 lane, the same model family as the packager (the cross-model review is the Opus pre-Lean review of a Sol proof).
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Garrity and Osterman (arXiv:2410.02032, Conjecture 53) conjectured that every S(e,23,e)-adic language of their TRIP-map family has factor complexity at most 3n. This holds for every directive sequence; the proof completes the bispecial-word strategy the authors outlined, with a new matching that controls bispecial lengths across levels. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $\mathcal{L}$ be an $S(e,23,e)$-adic language, and let $p_\mathcal{L}(n)$ denote its factor-complexity function. **Complexity bound conjecture.** The complexity function $p_\mathcal{L}$ for any $S(e,23,e)$-adic language $\mathcal{L}$ satisfies $$p_\mathcal{L}(n) \leq 3n.$$

## Summary of the result

For every directive sequence over the two substitutions of the TRIP-map family S(e,23,e), the factor complexity of the S-adic language satisfies p(n) ≤ 3n for every n ≥ 1; the bound is attained. The source proves the analogous bound for the family (e,e,e), outlines the method for (e,23,e) in its Section 10 with Propositions 69–71 stated without proof, and names the remaining work: characterize the bispecial words and control their lengths. The proof does this: every double-Gauss block is a 3-free word followed by a single 3, which gives unique parsing and the exact extension sets in both directions (the source's Proposition 71, here proved); the bispecial factors are classified into 23 types; and a new cross-age matching between bispecials of different levels controls their total extension count. Lean defines the two substitutions, the directive applied with d(0) outermost as the source's Definition 14 requires, the language as the factor closure of all images, and the complexity as the number of factors of length n, and proves the bound for every directive sequence, including degenerate ones such as the all-S1 sequence.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
