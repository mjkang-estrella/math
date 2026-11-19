# MathDB 359279: Two hook tableaux of size 12 with equal multisets of 8-minors: the k+4 reconstruction conjecture fails

- Problem: https://mathdb.com/p/359279
- Source: W. Q. Erickson et al., arXiv:2307.13161 Conjecture conj:k+4; JCTA 209 (2025) 105950; MathDB 359279
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `TabMinors.not_conjecture : ¬ TabMinors.Conjecture, where Conjecture := ∀ k n, 1 ≤ k → k + 4 ≤ n → ∀ T U, IsSYT n T → IsSYT n U → minors k T = minors k U → T = U`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `tabminors-draft.pdf`
- Lean source: `tabminors-source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: JCTA journal body unread (ScienceDirect route excluded); Monks and Cain-Lehtonen bodies not read; Jiradilok abstract only trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; the no-constant hook theorem and collision statistics beyond k = 8 are ordinary mathematics or diagnostics, not Lean not_claimed: A Lean proof of the no-constant theorem; The exact reconstruction threshold; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the k+4 reconstruction conjecture of Erickson, Herden, Meddaugh, Sepanski and coauthors, that for n >= k+4 the multiset of k-minors over all jeu de taquin deletions determines a standard Young tableau. Two hook tableaux of size 12, with first rows 1 5 7 8 12 and 1 2 3 7 10 11, are distinct with identical 8-minor multisets of 19558400 minors each; no bound n >= k+c works for fixed c, per a supplementary argument. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Erickson-Herden-Meddaugh-Sepanski-Hammon-Mohn-Ruiz-Bolanos (arXiv:2307.13161; J. Combin. Theory Ser. A 209 (2025) 105950), Conjecture conj:k+4: for n >= k+4 the multiset mM_k(T) of k-minors (over all jeu de taquin deletion sequences) determines a standard Young tableau. False at k = 8, n = 12. The hooks T1 (first row 1 5 7 8 12) and T2 (first row 1 2 3 7 10 11) are distinct and have identical mM_8 (19,958,400 minors each). Supplementary (ordinary mathematics, not Lean): a hook weight formula shows that no bound n >= k + c works for any constant c, with an explicit n = k+5 failure at k = 11.

## Body (paste into the MathDB body field)

Use the written proof in this folder: tabminors-draft.pdf. The complete Lean source is in tabminors-source-only.zip.
