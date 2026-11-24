# MathDB 368177: The uri multiplicities satisfy the threshold shuffle identities (Burmester–Kühn Conjecture A.7, with the middle word nonempty in identity (ii))

- Problem: https://mathdb.com/p/368177
- Source: Annika Burmester and Ulf Kühn, “On post-Lie structures for free Lie algebras”, arXiv:2504.19661 (2025), Conjecture A.7 with Definition A.5. https://arxiv.org/abs/2504.19661
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `TSI.conjecture_A7`, `TSI.tsi_i`, `TSI.tsi_ii`, `TSI.tsi_ii_tau_nil_false`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Counted under root's ruling on printed statements that fail only at a degenerate case: identity (ii) as printed has no condition on τ and is false for empty τ; the result is (i) in full and (ii) for nonempty τ, together with the Lean-checked counterexample to the printed (ii). The reviewer found that the authors plainly meant the nonempty case (their Theorem 5.11, Example A.6(ii) and Remark A.8), but a strict reader may say the conjecture as printed is refuted rather than proved. The consequences for post-Lie and Hopf-algebra structures (the source's Theorems 5.11 and 5.14) follow by the source's written argument and are outside Lean. Lean sets the multiplicities to 0 at non-positive thresholds. Closest prior work: Bachmann–Kawamura (arXiv:2609.29574) prove closure of the uri bracket for bimoulds, and Burmester–Kühn–Schneps (arXiv:2609.25168) give a bimould route, neither identifying these coefficient identities; omega issue 23147 and pull request 23270 resolve a different conjecture (4.29) of the same paper. No journal edition was found and the list of citing works is incomplete. Proof, first (same-model) review and Lean are by Claude Opus 5.5; the cross-model review and final check are by GPT-6.2 Sol (two rounds: the first rejected the literal statement, the second cleared the corrected statement at not routine 0.70).
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved, with a correction. Burmester and Kühn (arXiv:2504.19661, Conjecture A.7) conjectured that the uri multiplicities μ = B₁(length, index) satisfy their two threshold shuffle identities. Identity (i) holds in full and identity (ii) holds whenever the middle composition is nonempty, which is what their Theorem 5.11 uses; identity (ii) as printed fails for the empty middle composition (0 = −1 at the smallest case). The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $\mathcal{C}$ be the set of compositions, let $\ell(\boldsymbol{\alpha})$ be the length of a composition, and let $\operatorname{ind}_a(\boldsymbol{\alpha})$ be its index at $a$. Define the uri multiplicities by

$$
\mu_{a,\boldsymbol{\alpha}}=B_1(\ell(\boldsymbol{\alpha}),\operatorname{ind}_a(\boldsymbol{\alpha})),
$$

where

$$
B_1(m,n)=\frac{1}{m!}\sum_{k=0}^{n-1}\binom{m}{k}B_k.
$$

**Uri multiplicity threshold shuffle conjecture.** The uri multiplicities satisfy the threshold shuffle identities from the source's definition. The supplied text gives no resolution status for these identities.

## Summary of the result

The uri multiplicities satisfy threshold shuffle identity (i) of the source's Definition A.5 in full, and identity (ii) whenever the middle composition τ is nonempty; identity (ii) as printed, with no condition on τ, is false (at σ = τ = ∅, ϑ = (1), d₁ = d₂ = 0 it would assert 0 = −1). The corrected statement is what the source needs: the proof of its Theorem 5.11 uses (i) for adjacent factors and (ii) for factors separated by a nonempty word, its Example A.6(ii) follows that split, and the normalized solutions of its Remark A.8 are incompatible with the printed empty case. The proof expands the multiplicities over the cuts of a word, uses the compatibility of shuffle with deconcatenation and a divided-difference identity for the Bernoulli-type numbers B₁(m, n), and cancels the remaining alternating sum over cuts of the middle word, which is where τ ≠ ∅ enters. Lean states Definition A.5 and the multiplicities literally (with multiplicity 0 at non-positive thresholds, which implements the omission of inadmissible insertions), proves (i), proves (ii) for τ ≠ ∅, proves the counterexample to the printed (ii), and reproduces both parts of the source's Example A.6.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
