# MathDB 339235: Three induced colours on the Mobius ladder M_12: a refutation of the Lau-Shiu-Ng even Mobius ladder local antimagic conjecture

- Problem: https://mathdb.com/p/339235
- Source: Lau-Shiu-Ng, arXiv:1805.04888 Conjecture 3.2 (Discuss. Math. Graph Theory 41 (2021) 133-152, DOI 10.7151/dmgt.2177, Conjecture 3.14 per indexing); MathDB 339235
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Mobius.conjecture_false : ¬ (forall n, 4 <= n -> n % 2 = 0 -> Mobius.LocalAntimagicChromaticNumberEq n 4), where LocalAntimagicChromaticNumberEq n k states that the Mobius ladder M_2n (the 2n-cycle with antipodal chords) has a local antimagic labelling (a permutation of 1..3n with distinct sums across every edge) with exactly k distinct vertex sums and that every such labelling has at least k; witnessed by an explicit labelling of M_12 with three sums`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `proof-packet-full.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: 2020 workshop slides unread (Scribd access interface); journal body of Discuss. Math. Graph Theory 41 (2021) not fully accessed; indexing retains the conjecture as Conjecture 3.14; bounded citing-work body screen trust_limits: Lean 4.34.1 core trusted (Init only); leanchecker shares the installation not_claimed: chi_la(M_2n) for other even n; a Lean proof of the lower bound 3; priority; publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Lau-Shiu-Ng conjecture that even Mobius ladders have local antimagic chromatic number 4. The Mobius ladder M_12 on twelve vertices has local antimagic chromatic number 3: the failure of the value 4 is Lean-certified and the matching lower bound is the ordinary odd-cycle argument. A remark records that M_8 also has value 3, contradicting Theorem 2.4 of the same authors. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

chi_la(M_12) = 3 (Lean certifies the failure of the value 4; the matching lower bound 3 is an ordinary odd-cycle argument), refuting Lau-Shiu-Ng Conjecture 3.2 for even n >= 4; remark: chi_la(M_8) = 3 contradicts Lau-Shiu (arXiv:2203.06594, Acta Math. Hungar. 169 (2023)) Theorem 2.4

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in proof-packet-full.zip.
