# MathDB 347063: Linear-growth conjecture for Split Smallest and Combine Smallest games

- Problem: https://mathdb.com/p/347063
- Source: Ruoci Li, Xiaonan Li, Steven J. Miller, Clayton Mizgerd, Chenyang Sun, Dong Xia and Zhyi Zhou, “Deterministic Zeckendorf Games”, arXiv:2006.16457 (2020). (https://arxiv.org/abs/2006.16457); Conjecture 1.4 and the strategy priorities are in Li et al., arXiv:2006.16457
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Zeck.combine_smallest_asymptotic`, `Zeck.combine_constant_bracket`, `Zeck.split_smallest_asymptotic`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Record defect: the MathDB start position differs from the source; accepted on the source statement by root judgment (held for a user ruling since 2026-11-09; user may overrule). Significance modest. The proved error term is far from sharp (numerically the error stays under about 20 up to n = 3*10^7).
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved, for the source statement. In the deterministic Zeckendorf game started from n copies of F_1, the Combine Smallest strategy takes CS(n) = c n + O(sqrt(n) log n) moves, where c = 5/2 - phi + sum over j >= 2 of 1/F_{2j} = 1.20648..., which settles the Combine Smallest half of Conjecture 1.4; the Split Smallest half is due to Cusenza et al. Note: the MathDB record says the game starts from the Zeckendorf decomposition of n, which gives zero moves; the source starts from n ones, and that is the statement proved here. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

A Zeckendorf game starts from the Zeckendorf decomposition of $n$ and proceeds by legal combining and splitting moves; the **Split Smallest** and **Combine Smallest** games are deterministic strategies, and the number of moves is measured as the total number of moves in the resulting game.

**Linear-growth conjecture.** For Split Smallest, the number of moves grows linearly with $n$, with the asymptotic constant appearing numerically to be the square of the golden mean. For Combine Smallest games, the number of moves grows linearly with $n$, with the constant appearing numerically to be approximately $1.206$.

The paper presents these claims as data-supported conjectures for the two deterministic games whose behavior was not rigorously determined there.

## Summary of the result

Source-bound resolution of the Combine Smallest half of Conjecture 1.4 for the deterministic Zeckendorf game started from n copies of F_1: the number of moves is CS(n) = c n + O(sqrt(n) log n) with c = 5/2 - phi + sum_{j>=2} 1/F_{2j} = 1.2064811686..., with an explicit error constant. The Split Smallest half (constant phi^2) is due to Cusenza et al. and is only attributed. The MathDB record states the start position as the Zeckendorf decomposition of n, which gives zero moves and makes the record trivially false as literally written; the result proves the statement with the source start position.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
