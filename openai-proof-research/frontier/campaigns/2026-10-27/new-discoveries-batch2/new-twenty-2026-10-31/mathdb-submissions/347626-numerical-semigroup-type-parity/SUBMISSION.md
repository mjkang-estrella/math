# MathDB 347626: The type of a numerical semigroup has the parity of its Frobenius number half the time (Singhal's Conjecture 7.2)

- Problem: https://mathdb.com/p/347626
- Source: Deepesh Singhal, “Numerical Semigroups of small and large type”, arXiv:2008.08110 (2020), Conjecture 7.2. https://arxiv.org/abs/2008.08110
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Singhal.singhal_7_2`, `Singhal.singhal_7_2_encoded`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The limit is along all F, as in Conjecture 7.2 (the neighbouring Conjecture 7.3 concerns residue classes and is not addressed). The concentration of multiplicity near F/2 is due to Backelin (1990); Lean proves the one-sided estimate it needs and does not assume Backelin's theorem. The written proof by Claude Opus needed a local correction to a floor inequality found by the GPT-6.2 Sol review. The journal version of the source was not read (reviewer's probability that it settles the conjecture: 0.02); ProbXiv and the arXiv keyword API were unavailable. Proof and first (same-model) review are by Claude Opus 5.5 (the same-model review had rated it 0.5); the cross-model review (not routine 0.68), the Lean code and the final check (a separate lane) are by GPT-6.2 Sol, so the final check is by the same model family as the Lean packager.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Singhal (arXiv:2008.08110, Conjecture 7.2) conjectured that among numerical semigroups with Frobenius number F the proportion whose type is congruent to F modulo 2 tends to 1/2. Toggling the element ⌊3F/4⌋ pairs almost all such semigroups into pairs of opposite type parity; the exceptions are shown to be a vanishing fraction. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $F(S)$ be the Frobenius number of a numerical semigroup $S$, let $t(S)$ be its type, and let the denominator count all numerical semigroups with Frobenius number $F$. **Frobenius type-parity equidistribution conjecture.**

$$
\lim_{F\to\infty}\frac{\#\{S\mid F(S)=F,\ t(S)\equiv F\pmod{2}\}}{\#\{S\mid F(S)=F\}}=\frac{1}{2}.
$$

The conjecture is motivated by the same numerical data for $F\leq 30$ and predicts asymptotic equidistribution of the two type parities relative to the parity of $F$.

## Summary of the result

The conjecture holds: among numerical semigroups with Frobenius number F, the proportion whose type has the same parity as F tends to 1/2 as F grows, along all F. Almost all such semigroups have multiplicity close to F/2 (Backelin 1990; the one-sided form needed is proved here). For those, adding or removing the single element ⌊3F/4⌋ gives another numerical semigroup with the same Frobenius number, and the toggle changes the parity of the type unless the semigroup has pseudo-Frobenius numbers at one of a few small gaps from that element; a greedy count of disjoint pairs shows that the exceptional semigroups form a vanishing fraction. So the semigroups pair up, outside a negligible set, into pairs of opposite type parity. Lean defines numerical semigroups as cofinite additive submonoids of ℕ containing 0, the Frobenius number, the pseudo-Frobenius numbers and the type, and proves that the ratio of cardinalities tends to 1/2, both for the sets themselves and for a finite encoding used in the proof.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
