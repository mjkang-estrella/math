# MathDB 356756: A parity-corrected potential proves the Elsholtz–Klahn–Lipnik four-term progression-free digit-set conjecture

- Problem: https://mathdb.com/p/356756
- Source: C. Elsholtz, B. Klahn, G. F. Lipnik, arXiv:2211.02588v1 Conjecture 2.4; Des. Codes Cryptogr. 91 (2023) 1443-1452; MathDB 356756
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Digits356756.mathdb_356756 : for p prime, 13 <= p, p % 4 = 1, (p+3)/2 | n, there are no a b c d : Fin n -> ZMod p in SourceSet p n with zero second differences and a != b; Digits356756.no_affine_progression : no x + j r (j in Fin 4, r != 0) lies in SourceSet p n`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `digits-parity-draft.pdf`
- Lean source: `digits-source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: arXiv listing coverage for late 2026 bounded (one listing timed out; not retried); citing-work index imperfect (OpenAlex two records); Fuhrer 2024 thesis read in part trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; Stirling cardinality consequence and EHPS comparison are ordinary mathematics, not formalized not_claimed: A new record lower bound for r_4(Z_p^n) (EHPS 2406.12290 gives a larger base for p >= 41; source Table 1 has a larger set at p = 29); Maximality of D; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the Elsholtz-Klahn-Lipnik conjecture that for every prime p congruent to 1 mod 4 with p >= 13, and every n divisible by (p+3)/2, the digit set consisting of 0 through (p-1)/2 together with (p+3)/2 yields, among n-digit numbers, no nonconstant four-term arithmetic progression. The potential E(t) = 4t^2 - (3p-5)(-1)^t drives the proof, which does not even need primality. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Elsholtz-Klahn-Lipnik (Des. Codes Cryptogr. 91 (2023) 1443-1452, arXiv:2211.02588) Conjecture 2.4, repeated as Conjecture 4.6 in Lipnik's 2023 thesis: for every prime p >= 13, p = 1 mod 4, and every n divisible by (p+3)/2, S(D,n) with D = {0..(p-1)/2,(p+3)/2} has no nonconstant 4-term AP. Proved uniformly (primality unnecessary) via E(t) = 4t^2 - (3p-5)(-1)^t: the only wrapped coordinate progressions are (h-3,0,h,3) and (3,h,0,h-3), with gap 16; ordinary progressions have gap 16 s^2; equal digit frequencies force every gap to vanish.

## Body (paste into the MathDB body field)

Use the written proof in this folder: digits-parity-draft.pdf. The complete Lean source is in digits-source-only.zip.
