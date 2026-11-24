# MathDB 361823: One-step separation conjecture for genus Tutte polynomials

- Problem: https://mathdb.com/p/361823
- Source: Tsuyoshi Miezaki, Manabu Oura, Tadashi Sakuma and Hidehiro Shinohara, “The Tutte polynomials of genus g”, arXiv:2402.06845 (2024), Conjecture 5.12. https://arxiv.org/abs/2402.06845
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `GenusTutte.miezaki_conj_5_12`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The weight sits on g ≥ 4: for g ≤ 3 the pairs are the source's own matroids (R6/Q6, S_12/S'_12, S_16/S'_16), with a sharper equality analysis; the source's Theorem 4.22 as stated already gives g = 1, 2, but its proof relies on the source's Proposition 4.14, which the Lean-checked separations at n = 3, 4 contradict (a source erratum the final check found; the Lean proof uses no result of the source). 'Infinite sequences' is met by padding one pair per g with loops, the way the source obtains its own Proposition 5.10. The source's specialization identity on p. 4 is misprinted (counterexample proved). Cross-model reviewer: not routine 0.70. The Lean was written by a Claude Opus 5.5 lane from a GPT-6.1 Sol proof; the final check was by a separate Opus lane (same model family as the packager and the reviewer) because GPT-6.1 Sol hit its usage limit; a Sol re-check after 2026-11-26 is advisable.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Miezaki, Oura, Sakuma and Shinohara's one-step separation conjecture (arXiv:2402.06845, Conjecture 5.12): for every g ≥ 1 there are infinite sequences of matroids with equal genus-g and different genus-(g+1) Tutte polynomials. The new part (g ≥ 4) is a parity construction on sparse paving matroids with a rigidity lemma. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $g$ be a positive integer, and let $\{M_i\}$ and $\{N_i\}$ be sequences of matroids. **One-step separation conjecture.** There exist two infinite sequences of matroids $\{M_i\}$ and $\{N_i\}$ such that $T^{(g)}(M_i)=T^{(g)}(N_i)$ and $T^{(g+1)}(M_i)\neq T^{(g+1)}(N_i)$.

## Summary of the result

For every g ≥ 1 there are matroids with equal genus-g and different genus-(g+1) Tutte polynomials, so separation happens one genus up, the optimal constant in the source's Problem 5.11 (the source's Theorem 4.22 separates at genus ⌈√2·g⌉). For g ≥ 4 the new construction uses sparse paving matroids indexed by the even versus the odd vectors of {0,1}^g: an explicit bijection of g-tuples gives the equality at genus g, and a rigidity lemma (every output slot has a private input) shows that one extra slot detects the parity, giving a coefficient that differs at genus g+1. For g = 1, 2, 3 the pairs are the source's own examples (R6/Q6 and S_4n/S'_4n at n = 3, 4), with the equality and separation proved directly. Padding both matroids with i loops gives the infinite sequences. Lean defines the genus-g Tutte polynomial over Mathlib's matroids with the source's slot variables (singletons and pairwise intersections and unions), and proves the statement for every g with no hypothesis and nothing cited from the source.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
