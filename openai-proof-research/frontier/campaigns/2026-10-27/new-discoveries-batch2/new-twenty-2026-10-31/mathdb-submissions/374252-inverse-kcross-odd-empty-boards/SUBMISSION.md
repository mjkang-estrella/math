# MathDB 374252: Sprague–Grundy values of empty boards of Inverse k-cross for odd k (the generalized reflectional periodicity conjecture of Liang and Li)

- Problem: https://mathdb.com/p/374252
- Source: Kai Liang and Muxi Li, “A Weak Solution of Inverse Treblecross”, arXiv:2604.16759 (2026), Conjecture 5.5 of version 1 (Conjecture 5.4 of version 2). https://arxiv.org/abs/2604.16759
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `OddInverseKCross.odd_inverse_kcross_bit`, `OddInverseKCross.odd_inverse_kcross_translation`, `OddInverseKCross.odd_inverse_kcross_reflection`, `OddInverseKCross.odd_inverse_kcross_formula`, `OddInverseKCross.boardCuts_source_move_iff`, `OddInverseKCross.odd_inverse_kcross_nonvacuous`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The source prints no range for a; the translation identity is proved for every a ≥ 0 and the reflection identity for 0 ≤ a ≤ 5m+2, the range in which both boards exist (Lean also covers the degenerate m = 0). Lean works with the sets of unmarked cells; the match with the source's board is kernel-checked move for move, and the equality of Sprague–Grundy values on the two models follows by a short induction that is not a separate Lean theorem. The argument is short and elementary (one page); the source's authors proved only k = 3, by a longer method, and wrote that their method is insufficient for general odd k. This is the second counted result from arXiv:2604.16759 after 374250, a different conjecture (Section 5.1, one-piece positions at k = 3) proved by a different method; neither follows from the other. No journal version of the source is known. All work is by AI and no human has checked it: the proof, the Lean code and the paper are by GPT-6.2 Sol lanes; the adversarial review before Lean (not routine 0.75) and the final check (not routine 0.70) are by two separate Claude Opus 5.5 lanes. The Semantic Scholar citation list was rate-limited; OpenAlex was used for citations.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Liang and Li (arXiv:2604.16759, Conjecture 5.5 of v1, 5.4 of v2) conjectured that for odd k = 2m+1 the empty boards of Inverse k-cross have Sprague–Grundy value at most 1 and satisfy a translation and a reflection identity. In fact the value of the board of length n is (n + [n mod (3m+2) ≥ k]) mod 2: a block strategy lets either player force the number of empty cells at the end, so the length of the game is fixed. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $k=2m+1$ with $m\geq1$, and consider an Inverse $k$-cross game with empty-board state $[a]$. Let $\mathcal{G}([a])$ denote its Sprague–Grundy value, and let $\oplus$ denote nim-sum. **Generalized reflectional periodicity conjecture.** For every such game, $\mathcal{G}([a])\leq1$, and

$$
\mathcal{G}([2+3m+a])=\mathcal{G}([a])\oplus(m\bmod2),
$$

$$
\mathcal{G}([2+5m-a])=\mathcal{G}([a])\oplus(m\bmod2).
$$

For $k=2$, eventual periodicity is known through the identification with Dawson's Kayles, whereas for even $k>2$ eventual periodicity is unknown; the asserted uniform bound and reflectional periodicity for odd constraints remain conjectural.

## Summary of the result

The conjecture holds, and more is true: for every odd k = 2m+1 the Sprague–Grundy value of the empty board of length n is (n + [n mod (3m+2) ≥ k]) mod 2. With P = 3m+2, either player can force the game to end with exactly 2⌊n/P⌋ + [n mod P ≥ k] empty cells, even when one extra nim-heap of size one is added: the board is cut into blocks of k + (m+1) cells, each containing m+1 disjoint supports and only m high cells, and the defender answers inside the block the opponent just played in. So the length of the game is fixed and its parity gives the value; the bound G ≤ 1 and both identities follow from the formula. Lean defines the game on the sets of unmarked cells (a position is legal when every window of k cells contains an unmarked cell), the options and the Sprague–Grundy value as a minimum excluded value, proves the three statements of the conjecture and the closed formula for every m ≥ 0, and proves that the moves of this model are, move for move, the placements of the source's game on a Boolean board.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
