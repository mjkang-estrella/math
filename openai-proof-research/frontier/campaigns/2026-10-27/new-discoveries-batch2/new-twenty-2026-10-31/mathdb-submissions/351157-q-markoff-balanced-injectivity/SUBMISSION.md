# MathDB 351157: The q-analog of the Markoff injectivity conjecture over balanced sequences

- Problem: https://mathdb.com/p/351157
- Source: Sébastien Labbé and Mélodie Lapointe, “The q-analog of the Markoff injectivity conjecture over the language of a balanced sequence”, arXiv:2106.15886 (2021), Conjecture 1.3; journal version in Combinatorial Theory. https://arxiv.org/abs/2106.15886
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `labbe_lapointe_conj_1_3`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. A specialist could call the derivative at the sixth root of unity the natural next step after the published evaluation there; the cross-model reviewer puts 0.70 on not routine and 0.75 on the verdict. The citing-paper check rests on Semantic Scholar's list, with five papers read at abstract level only. No second cross-model lane read the finished Lean: root compared the final theorem and every definition with the endpoint the Claude Opus reviewer had written (identical), and the GPT-6.1 Sol final check compared the definitions with the source and found no collision among the 3,695 balanced words of length at most 18.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. The q-analog of the Markoff injectivity conjecture holds over the whole language of balanced sequences (Labbé and Lapointe, arXiv:2106.15886, Conjecture 1.3): w ↦ μ_q(w)_{12} is injective on all finite factors of balanced bi-infinite binary sequences. The key step is the first derivative at a primitive sixth root of unity, which recovers two position statistics that, with the letter counts, determine a balanced word. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $\mathcal{B}=\{s\in\{\mathtt{0},\mathtt{1}\}^{\mathbb{Z}}:s\text{ is balanced}\}$ be the set of all balanced bi-infinite binary sequences, and let $\mathcal{L}(\mathcal{B})=\bigcup_{s\in\mathcal{B}}\mathcal{L}(s)$ be their language of finite factors. Let $\mu_q$ be the $q$-analog of the Markoff map assigning to a finite word $w$ the matrix whose $(1,2)$ entry is $\mu_q(w)_{12}\in\mathbb{Z}[q]$. **The $q$-analog of the Markoff injectivity conjecture over balanced sequences.** The map $w\mapsto\mu_q(w)_{12}$ is injective over $\mathcal{L}(\mathcal{B})$.

## Summary of the result

The polynomial μ_q(w)_{12} determines w among all finite factors of balanced bi-infinite binary sequences. The published tool, evaluation at a primitive sixth root of unity (Labbé, Lapointe and Steiner 2023, who proved injectivity on Christoffel words), recovers only the letter counts, and two balanced words from different sequences can have the same counts. The new step is the first derivative at that root: the two-letter commutator vanishes there, so the derivative is a function of two integer statistics recording where the ones sit. A second argument shows that a balanced word is the unique minimizer of a separable quadratic energy among words with its length and counts, so the length, the number of ones and the two statistics determine the word. Lean states the source's matrices, the left-to-right product and the (1,2) entry, balanced sequences on ℤ and their language, and checks the source's example polynomial, a pair of balanced words with equal counts lying in no common balanced sequence, and the known non-injective pair outside the language.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
