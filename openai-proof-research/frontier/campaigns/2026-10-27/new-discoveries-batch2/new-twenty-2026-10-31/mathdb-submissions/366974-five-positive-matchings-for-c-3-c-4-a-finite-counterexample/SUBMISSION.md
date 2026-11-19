# MathDB 366974: Five positive matchings for C_3 □ C_4: a finite counterexample to Conjecture 4.7 of arXiv:2502.02826

- Problem: https://mathdb.com/p/366974
- Source: Farrokhi-Yazdan Pour arXiv:2502.02826 Conjecture 4.7; MathDB 366974
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `TorusPMD.refutes_conjecture_4_7 : ¬ ∀ m n, 3 ≤ m → 3 ≤ n → Even (m + n) ∨ (m, n) = (3, 4) ∨ (m, n) = (3, 6) ∨ (m, n) = (5, 6) → pmd (torus m n) = 6, with pmd the literal minimum positive matching decomposition number on the Cartesian product of cycles`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `lean-packet.tar.gz`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: citation indexes incomplete; Google Scholar, MathSciNet and zbMATH not consulted; Genova thesis read only in its relevant sections, via a copy fetched with TLS verification disabled trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; the audit covers the 24 local declarations (axioms and metadata), not a full upstream closure inventory; the supporting cases and the exact value 5 are ordinary mathematics, not Lean claims not_claimed: Separate credit for (3,5), (3,6) or (3,7); A formula for pmd of all tori; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Conjecture 4.7 of Farrokhi D. G. and Yazdan Pour, that the paired positive matching number of the torus grid C_m by C_n equals 6 in the listed cases. The 3 by 4 torus C_3 by C_4 admits a positive matching decomposition into five parts, and its value is exactly 5; supporting certificates give 5 also at sizes (3,5), (3,6) and (3,7). The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Farrokhi D. G. and Yazdan Pour, arXiv:2502.02826v1, Conjecture 4.7 (pmd(C_m □ C_n) = 6 for m + n even or (m, n) in {(3,4), (3,6), (5,6)}). False: C_3 □ C_4 has a five-part positive matching decomposition, and pmd(C_3 □ C_4) = 5 exactly; supporting certificates show pmd = 5 also at (3,5), (3,6) and (3,7).

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in lean-packet.tar.gz.
