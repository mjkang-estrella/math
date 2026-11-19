# MathDB 350721: A negative coefficient for every n >= 8 in the Alexandersson-Kebede cycle-restricted signed sum: a refutation of Conjecture 5.2.1 (Australas. J. Combin. 86(3) (2023))

- Problem: https://mathdb.com/p/350721
- Source: Alexandersson-Getachew Kebede, Australas. J. Combin. 86(3) (2023) 387-413, Conjecture 5.2.1; arXiv:2105.08455v3; MathDB 350721
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `AK350721.conjecture_refuted : ¬ AK350721.VoRConj ∧ ¬ AK350721.MathDBConj, where VoRConj := for all n k with 2 <= k <= n, (-1)^(n-1) * sum over pi in Perm (Fin n) with every part of pi.partition at least k of (-1)^invCount(pi) * x_rlmv(pi) * y_excv(pi) lies in the image of MvPolynomial.map (Nat.castRingHom Z), and MathDBConj is the same without the sign factor for 1 <= k <= n; both witnessed at (n,k) = (9,3) by the coefficient -1 of x_{1,5,7,8} y_{2,3,4,6,9}`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `manuscript.pdf`
- Lean source: `source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: bounded citing-work coverage (OpenAlex: 2 citing works, Pei-Zeng's 1 citing work; Crossref, Semantic Scholar and Google Scholar not used); Ji-Zhang 2024 body unread trust_limits: Lean 4.34.1 core/Std and pinned mathlib trusted; leanchecker shares the installation not_claimed: a classification of negative monomials; positivity or failure for k >= 5; priority; publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Conjecture 5.2.1 of the Australasian Journal of Combinatorics on the Alexandersson-Kebede cycle-restricted signed sum: the sum has a negative coefficient at k = 3 for every n >= 8, certified formally at n = 9 in both the journal and the database wording, while it holds for all 2 <= k <= n when n <= 7, by computation. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Conjecture 5.2.1 fails at k = 3 for every n >= 8 (ordinary proof; Lean certifies n = 9 for both the version-of-record and the MathDB/arXiv v3 wording); it holds for all 2 <= k <= n when n <= 7 (computation)

## Body (paste into the MathDB body field)

Use the written proof in this folder: manuscript.pdf. The complete Lean source is in source.zip.
