# MathDB 356266: An Euler tour of the full permutation overlap graph that no cyclic word realizes: a refutation of Hurlbert's ordering conjecture for universal cycles of permutations

- Problem: https://mathdb.com/p/356266
- Source: Kirsch-Sibley-Sprangel, arXiv:2209.14198, Conjecture 6.3; Hurlbert 1990 thesis Conjecture 3.1.3 and Chung-Diaconis-Graham 1992 Section 4 (as cited); MathDB 356266
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `MathDB356266.conjecture_false : ¬ MathDB356266.Conjecture, where Conjecture := for all n N and every t : Fin (N+1) -> Fin (n+1) -> Fin (n+1) with EulerOrdering t (every row a permutation, rows distinct, every permutation occurring, every cyclic consecutive pair overlapping after reduction) there are K and a cyclic word w : Fin (N+1) -> Fin K whose windows realize t; also MathDB356266.conjectureLinear_false for words over an arbitrary linear order`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `manuscript.pdf`
- Lean source: `proof-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: Hurlbert's 1990 thesis body unread; Jackson 1993 body unread; the source's journal version (Adv. Appl. Math. 2023, DOI 10.1016/j.aam.2023.102522) unread; retention evidence: the arXiv text and the 2022 companion arXiv:2204.02910 (Kirsch-Lidicky-Sibley-Sprangel) both state the all-tour question as open; CDG citing works screened by title only; folklore not excluded trust_limits: Lean 4.34.1 core/Std and pinned mathlib trusted; leanchecker shares the installation not_claimed: the proportion or classification of non-realizable tours; results for n >= 5; priority; publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Hurlbert's ordering conjecture, repeated as Conjecture 6.3 of Kirsch, Sibley and Sprangel and as the 1992 Chung-Diaconis-Graham belief, that every Euler tour of the permutation overlap graph is realized by a universal cycle of permutations. At n = 4, an explicit Euler tour of the clustered overlap graph is realized by no cyclic word over any linearly ordered alphabet. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Hurlbert's ordering conjecture (Kirsch-Sibley-Sprangel Conjecture 6.3; Hurlbert 1990; the Chung-Diaconis-Graham 1992 belief) is false at n = 4: an explicit Euler tour of the clustered overlap graph O(4) is realized by no cyclic word over any linearly ordered alphabet

## Body (paste into the MathDB body field)

Use the written proof in this folder: manuscript.pdf. The complete Lean source is in proof-source.zip.
