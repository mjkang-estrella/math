# MathDB 338258: A 15-vertex counterexample to the odd-kernel conjecture for io-decomposable Riordan graphs

- Problem: https://mathdb.com/p/338258
- Source: Cheon-Jung-Kitaev-Mojallal arXiv:1801.07021 Conjecture 7.7; MathDB 338258
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Riordan.source_conjecture_false : ¬ SourceConjecture (finite Definition 2.9, canonical odd copy) and Riordan.source_conjecture_false_infinite_family : ¬ SourceConjectureInfiniteFamily (every integer series a with a_0 odd and a_(2j+1) ≡ a_j mod 2, every n ≥ 2, singular G_n(a, za), every real 0-eigenvector has zero odd part)`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `338258-infinite-family-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: final publisher body unread (accepted manuscript read); Spectral properties of Pascal graphs body not obtained; citing-work census incomplete trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; minimality within the recurrence family and nullity are ordinary computation, not Lean claims not_claimed: A corrected odd-kernel criterion; The finite-definition n = 7 twin example as a result; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Conjecture 7.7 of Cheon, Jung, Kitaev and Mojallal, that a singular io-decomposable Riordan graph G_n(g,zg) has kernel vector with zero odd part. The polynomial g = 1+z+z^3+z^6+z^7+z^8+z^12+z^13 at n = 15 gives a connected io-decomposable Bell Riordan graph of nullity 1 whose kernel vector has odd part (-1,0,-1,0,1,0,1,1); the same graph arises from an infinite series satisfying the source's Lemma 2.11 identity. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Cheon, Jung, Kitaev and Mojallal, Riordan graphs II: Spectral properties, arXiv:1801.07021v1 (journal accepted manuscript in the Strathclyde repository retains it), Conjecture 7.7: for a singular io-decomposable Riordan graph G_n(g, zg), X_o = 0. False: g = 1+z+z^3+z^6+z^7+z^8+z^12+z^13 at n = 15 gives a connected io-decomposable Bell Riordan graph of nullity 1 whose kernel vector has odd part (-1,0,-1,0,1,0,1,1); the same graph arises from an infinite series satisfying the Lemma 2.11 identity at every index.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in 338258-infinite-family-source.zip.
