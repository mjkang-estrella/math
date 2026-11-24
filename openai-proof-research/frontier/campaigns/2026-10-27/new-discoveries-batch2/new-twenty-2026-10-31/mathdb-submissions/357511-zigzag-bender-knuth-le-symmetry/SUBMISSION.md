# MathDB 357511: The even zigzag-poset LE-symmetry conjecture

- Problem: https://mathdb.com/p/357511
- Source: Judy Hsin-Hui Chiang, Anh Trong Nam Hoang, Matthew Kendall, Ryan Lynch, Son Nguyen, Benjamin Przybocki and Janabel Xia, “Bender-Knuth involutions on linear extensions of posets”, arXiv:2302.12425 (2024), Conjecture 4.17. https://arxiv.org/abs/2302.12425
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Zigzag.even_zigzag_LE_symmetric`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The Lean route differs from the original written proof in two places (block propagation plus Jordan's theorem instead of normal-closure support propagation; a tail sign recurrence instead of Euler-number congruences); the revised paper follows the Lean route. The citation index was enumerated through OpenAlex only. The formalization took eight stages, two of them in parallel. Cross-model confidence 0.80, not routine 0.80. No second cross-model lane read the finished Lean: root compared the final theorem and every definition with the endpoint the Claude Opus reviewer had written (same statement; ZigzagLE an abbreviation of the required subtype; the move proved equal to the literal incomparability swap), and the GPT-6.1 Sol final check confirmed the full symmetric groups S_5, S_61 and S_1385 for n = 4, 6, 8 by independent computation.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. For every even n the Bender–Knuth involutions generate the full symmetric group on the linear extensions of the zigzag poset Z_n (Chiang et al., arXiv:2302.12425, Conjecture 4.17; previously verified only for n ≤ 10). The proof combines a 3-cycle from a commutator, primitivity and Jordan's theorem, and an odd generator. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

For even $n$, let $Z_n$ be the poset on $n$ elements with relations $v_1 < v_2 > v_3 < v_4 > \ldots > v_{n-3} < v_{n-2} > v_{n-1} < v_n$. A poset is **LE-symmetric** when its Bender–Knuth group acts as the full symmetric group on its set of linear extensions. **The even zigzag-poset LE-symmetry conjecture.** The zigzag poset $Z_n$ is LE-symmetric when $n$ is even.

## Summary of the result

For every even n the Bender–Knuth involutions generate the full symmetric group on the linear extensions of the zigzag poset Z_n (whose number is an Euler number: 5, 61, 1385, ...). The source verified n ≤ 10 by computer and proved only transitivity. The proof is an induction on n: removing the last two elements embeds the action for n − 2, and a commutator of moves supported on different blocks isolates a 3-cycle; the group is primitive because a block containing one fibre is forced to be everything, so Jordan's theorem gives the alternating group; finally the second Bender–Knuth move is an odd permutation, by a sign recurrence through the tail fibres. Lean defines Z_n literally (an even-indexed element is below its neighbours), linear extensions as position-to-vertex bijections respecting the order, the Bender–Knuth move as the swap of adjacent positions when the two elements are incomparable (proved equivalent to the literal rule), and checks the counts 5 and 61 so that the statement cannot hold by an empty or trivial set.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
