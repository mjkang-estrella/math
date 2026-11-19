# MathDB 333709: No two-round minimal line-percolating set in PG(2,5): a counterexample to Conjecture 20 of Gerbner-Keszegh-Meszaros-Patkos-Vizer (arXiv:1608.00531)

- Problem: https://mathdb.com/p/333709
- Source: Gerbner-Keszegh-Meszaros-Patkos-Vizer arXiv:1608.00531v1 Conjecture 20 (SIAM J. Discrete Math. 32(2) (2018) 864-881); MathDB 333709
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Percolation.not_conjecture20_unconditional : ¬ Percolation.Conjecture20, where Conjecture20 := for every q, every finite projective plane P of order q (literal incidence axioms with a quadrangle) and every r with 4 <= r <= q there is an infection a with Minimal P r a (percolates and no proper subset percolates) and TimeIs P r a 2 (full at round 2 and not earlier), for synchronous r-threshold line percolation`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: SIAM J. Discrete Math. version of record unread; bounded citing-work coverage trust_limits: Lean 4.34.1 core/Std build trusted; leanchecker shares the installation; no short human proof is known not_claimed: A theorem for other orders; Minimal counterexample status; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Conjecture 20 of Gerbner, Keszegh, Meszaros, Patkos and Vizer on minimal percolating sets. At the boundary case (q,r) = (5,5), the projective plane PG(2,5) admits no inclusion-minimal percolating set with percolation time 2 under line percolation at threshold 5. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Conjecture 20 fails at the allowed boundary (q,r) = (5,5): in PG(2,5) no inclusion-minimal percolating set has percolation time 2 at threshold 5.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in source-only.zip.
