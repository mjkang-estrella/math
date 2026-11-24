# MathDB 354240: Thue–Morse arithmetic-progression bound conjecture

- Problem: https://mathdb.com/p/354240
- Source: Bartosz Sobolewski, “On monochromatic arithmetic progressions in binary words associated with pattern sequences”, arXiv:2204.05287 (2023). https://arxiv.org/abs/2204.05287
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Campaign354240Literal.sobolewski_conjecture_three`, `Campaign354240Literal.sobolewski_conjecture_three_bundled`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Bounded literature search only; the full text of Joshi's 2025 thesis was not read (its abstract does not mention this bound). The key arc lemma is short once seen (cross-model confidence: correct 0.95, not public 0.85, not routine 0.75). The discovery lane's first Lean endpoint used a quantity capped at d + 5 by definition, which made the bound true by definition; the cross-model reviewer caught this, and the endpoint listed here is the uncapped one, added in a separate 123-line module that root read and the GPT-6.1 Sol final check verified; no second cross-model lane read that module. The Lean definition follows the corrected definition of arXiv v2 and the journal (v1's definition of the supremum was defective). Closest prior work: Morgenbesser, Shallit and Stoll (d + 4 for progressions starting at 0); Parshina; Aedo, Grimm, Nagai and Staynova; Joshi and Rust, arXiv:2501.05830.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. In the Thue-Morse sequence, a monochromatic arithmetic progression of difference d has length at most d + 5, with equality for some starting point exactly when d = 2^k - 1 with k even, k >= 2. This is Conjecture 3 of Sobolewski (arXiv:2204.05287). The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $\mathbf{t}$ denote the Thue–Morse sequence, and let $A_{\mathbf{t}}(d)$ be its associated arithmetic-progression counting function.

**Thue–Morse bound conjecture.** For all $d \geq 1$,

$$
A_{\mathbf{t}}(d) \leq d+5.
$$

Moreover, equality holds if and only if $d=2^k-1$ for some even $k \geq 2$.
The conjecture gives a sharp linear upper bound, with equality at the indicated powers-of-two-minus-one parameters.

## Summary of the result

For every difference d >= 1, the longest monochromatic arithmetic progression of difference d in the Thue-Morse sequence has length A_t(d) <= d + 5, and A_t(d) = d + 5 exactly when d = 2^k - 1 with k even and k >= 2 (d = 3, 15, 63, 255, ...). This is Conjecture 3 of Sobolewski, for every starting point and both colours. The proof places a binomial cube S_D with D >= c - 5 inside the set of residues where the colour is forced to change, by Lucas's theorem; shows over F_2 that X^{uj}(1 + X^u)^D is divisible by (1 + X)^D, so that after multiplication by any odd u this set cannot fit in a cyclic arc shorter than D, which gives the bound; and characterizes equality by a rigidity lemma for affine cubes and three explicit families of obstructions. Lean defines the length with no cap, as the supremum over starting points of the first index at which the colour changes, in the extended naturals.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
