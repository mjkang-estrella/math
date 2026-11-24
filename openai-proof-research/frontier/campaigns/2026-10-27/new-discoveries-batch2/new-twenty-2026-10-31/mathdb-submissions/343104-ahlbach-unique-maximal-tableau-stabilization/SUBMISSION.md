# MathDB 343104: Unique permutation with maximal stabilization

- Problem: https://mathdb.com/p/343104
- Source: Connor Ahlbach, “Tableau Stabilization and Rectangular Tableaux Fixed by Promotion Powers”, arXiv:1907.00105 (2019). (https://arxiv.org/abs/1907.00105)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `TableauStabilization.mathdb_343104`, `TableauStabilization.stab_id`, `TableauStabilization.stab_le_pred_of_ne_one`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The kernel-checked definition of stabilization is the row-insertion form; the bridge to the source's rectification form is the classical identity Rect(S) = P(reading word of S) (source Lemma 2.10, from Fulton), trusted and not formalized. An independent referee computed stabilization both ways for all 46,233 permutations with n <= 8 and found agreement, and agreement with Ahlbach's published distribution. Bounded literature search; two citation indexes refused requests.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. For every n >= 1, a permutation of size n has stabilization index n if and only if it is the identity; every other permutation stabilizes by n-1. This is Ahlbach's conjecture (arXiv:1907.00105) that the increasing permutation is the unique permutation with maximal stabilization. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $w$ be a permutation of $\{1,2,\dots,n\}$, viewed as a tableau, and let $\stab(w)$ denote its stabilization time. **Maximal-stabilization conjecture.** The increasing permutation

$$
w=1\,2\,\dots\,(n-1)\,n
$$

is the only permutation with $\stab(w)=n$. This asks for the rightmost entry in the stabilization distribution on permutations to be unique. The statement is posed as an open problem after the paper notes that the leftmost entry is always $1$; its truth is not established there.

## Summary of the result

For every n >= 1 and every permutation w of size n, the stabilization index of w equals n if and only if w is the identity: the increasing permutation stabilizes at n, and every permutation with a descent stabilizes by n-1. This proves Ahlbach's conjecture that the increasing permutation is the unique permutation with maximal stabilization. Lean defines stabilization through the row-insertion tableau of the k-fold reading word and checks that every entry of the last copy stays in its original row; the identification of this with the source's definition by jeu de taquin rectification is the source's Lemma 2.10 (a classical theorem of Schutzenberger, cited from Fulton), which is not checked in Lean. The hypothesis n >= 1 is needed and matches the source.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
