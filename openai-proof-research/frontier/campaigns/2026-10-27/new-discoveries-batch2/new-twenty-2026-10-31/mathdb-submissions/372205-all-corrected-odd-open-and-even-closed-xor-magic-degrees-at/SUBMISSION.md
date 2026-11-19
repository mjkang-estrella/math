# MathDB 372205: All corrected odd-open and even-closed XOR-magic degrees at powers of two

- Problem: https://mathdb.com/p/372205
- Source: S. Cichacz, H. Grochowski, R. Zuazua, arXiv:2512.19278v1 Conjecture 25; MathDB 372205
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `XorMagic.corrected_all : ∀ n : ℕ, 4 ≤ n → CorrectedAt n; XorMagic.not_printed_each_ge_four : ∀ n : ℕ, 4 ≤ n → ¬ PrintedAt n (also printed_not_all, printed_not_positive)`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `xor-magic-draft.pdf`
- Lean source: `xor-magic-manuscript-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; Batal DAM 2026 body unread (publisher 403, repository challenge), but Batal posed the existence question as open; not worldwide priority remaining_literature_limits: Batal, Discrete Applied Mathematics 379 (2026) 288-315 body unread; citing-work coverage bounded trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; base graphs found by optimizer search, verified exactly by kernel decide not_claimed: Novelty of the Proposition 24 endpoint correction; Graph classification; Other parity classes or labelling groups; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the complete existence picture for connected simple zero-XOR graphs on 2^n vertices. As printed, the Cichacz-Grochowski-Zuazua conjecture is false for every n >= 4, its closed-degree list omitting degrees excluded by the known nonexistence result; under the intended correction, the odd open degrees 5 through 2^n-5 and the even closed degrees 4 through 2^n-6 all occur, which with that result is exhaustive. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Cichacz-Grochowski-Zuazua Conjecture 25 (arXiv:2512.19278) as printed is false at every n>=4 because closed degree 2^n-4 is excluded by Proposition 24 (Batal); that correction is zero-credit. The intended conjecture (MathDB: 'apart from the degrees excluded by the previously stated nonexistence result') is proved in full: for every n>=4 there are connected simple open zero-XOR graphs on 2^n vertices of every odd degree 5..2^n-5 and closed ones of every even degree 4..2^n-6, which with Proposition 24 is the complete existence picture for the odd-open and even-closed classes.

## Body (paste into the MathDB body field)

Use the written proof in this folder: xor-magic-draft.pdf. The complete Lean source is in xor-magic-manuscript-source.zip.
