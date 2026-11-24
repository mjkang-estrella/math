# MathDB 374250: Completeness of the regular set of Inverse Treblecross positions with at most one piece (Liang–Li Conjecture 5.1)

- Problem: https://mathdb.com/p/374250
- Source: Kai Liang and Muxi Li, “A Weak Solution of Inverse Treblecross”, arXiv:2604.16759 (2026), Conjecture 5.1 of version 1. https://arxiv.org/abs/2604.16759
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `ITB.conjecture_5_1`, `ITB.conj_5_1`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The statement proved is Conjecture 5.1 of arXiv version 1, which the MathDB record follows. Version 2 (October 2026) restricts the main quantifier to gaps a, b ≥ 2 while still listing the same four exceptions (only [4X4] lies in that range) and contains an inconsistent remark about boundary states; the theorem implies version 2's restricted claim and the stated facts about the exceptions. A modest result: the source already gives the regular values and the four exceptions, and finite-certificate periodicity arguments are standard for such games; the cross-model reviewer put not-routine at 0.58, close to the floor of 0.55 root uses for counting. The counts of certificate entries reported in the paper (589 family entries, 77 further one-piece entries, the historical cutoff 52) come from Python checks and are not part of the Lean dependency chain; the Lean certificate is self-contained. Proof and first (same-model) review are by Claude Opus 5.5; the cross-model review is by GPT-6.2 Sol; the Lean is by Claude Opus 5.5 (stage 1) and GPT-6.2 Sol (stage 2); the definitions were checked by GPT-6.1 Terra and the final check was completed by a separate GPT-6.2 Sol lane (same model family as the stage-2 packager). Semantic Scholar and ProbXiv were unavailable to the final check.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Liang and Li (arXiv:2604.16759v1, Conjecture 5.1) conjectured that in Inverse Treblecross the boards with at most one piece and Sprague–Grundy value at most 1 are exactly their regular set R plus four exceptional boards [1X1], [1X4], [4X1], [4X4]. This is proved for boards of every length, by an induction over an auxiliary family of two-piece boards with a finite residue-periodic certificate. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $R$ be the regular set of board states, let a state have at most one piece, and let $\mathcal{G}$ denote its Sprague–Grundy value. **Completeness conjecture.** The regular set $R$ contains all board states that possess at most one piece and satisfy $\mathcal{G} \le 1$, with exactly four isolated exceptions:

$$
[1 X 1],\quad [1 X 4],\quad [4 X 1],\quad \text{and}\quad [4 X 4].
$$

These four states are described as isolated anomalies, and empirical data indicates that all other sufficiently long states in their residue classes have $\mathcal{G}>1$; the completeness of $R$ beyond the stated exceptions remains unproved.

## Summary of the result

The conjecture (as printed in version 1 of the source, which the MathDB record follows) holds: among boards of Inverse Treblecross with at most one X, those with Sprague–Grundy value at most 1 are exactly the boards of the regular set R together with [1X1], [1X4], [4X1] and [4X4], and each of these four has value exactly 1 and lies outside R. The source computes the values on R and tabulates small cases; what was missing is that no other board, of any length, has value at most 1. Mixed-residue cases are settled in two moves from the source's values for empty boards. When both gaps lie in the critical residue classes, a move at distance four supplies the missing option once the values of an auxiliary family of two-piece boards are known, and those are certified by a coupled induction: a finite abstract-interpretation certificate (each gap known exactly when small, otherwise by its residue modulo 10) checked for all gap lengths at once. Lean defines the game literally on lists of Booleans (a move fills an empty cell without creating three adjacent X's; the value is the mex of the option values), proves the certificate checker sound, proves that the certificate covers every concrete gap length, and proves the classification.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
