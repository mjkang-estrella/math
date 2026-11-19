# MathDB 369421: A 45-letter word refuting the toroidal-grid representation-number conjecture of Alshammari, Kitaev and Pyatkin (arXiv:2507.16469, Conjecture 1)

- Problem: https://mathdb.com/p/369421
- Source: Alshammari-Kitaev-Pyatkin arXiv:2507.16469v1 Section 4 Conjecture 1 (to appear in J. Automata, Languages and Combinatorics); MathDB 369421
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Toroidal.mathdb_369421 : ¬ Toroidal.Conjecture1, where Conjecture1 := ∀ m n : ℕ, 3 ≤ m → 3 ≤ n → 8 ≤ m + n → 4 ≤ representationNumber m n; representationNumber = least positive k such that some list over Fin m × Fin n uses every vertex exactly k times and, for distinct vertices, alternation of the two-letter subword holds iff they are adjacent in C_m □ C_n (⊤ if none)`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `manuscript.pdf`
- Lean source: `lean-packet.tar.gz`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: accepted JALC manuscript embargoed to 2099 and unread (author list and repository link the accepted paper to this arXiv text); bounded citing-work screens (OpenAlex coverage incomplete); Google Scholar and MathSciNet not consulted trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; the audit covers the 23 packet declarations (axioms and metadata), not a full upstream closure inventory; the search method is not claimed new (Akgun-Gent-Kitaev-Zantema 2019 give a generic SMT encoding) not_claimed: R(C_3 □ C_5) = 3 exactly; Any other toroidal case; A new search method; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Alshammari-Kitaev-Pyatkin conjecture that the representation number of the Cartesian product of two cycles of lengths at least 3 with lengths summing to at least 8 is at least 4. An explicit 45-letter word over three symbols represents the torus grid C_3 by C_5, so that graph's representation number is at most 3. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Alshammari-Kitaev-Pyatkin Conjecture 1: R(C_m □ C_n) ≥ 4 for m, n ≥ 3 and m + n ≥ 8. False at (3, 5): an explicit 45-letter 3-uniform word represents C_3 □ C_5, so its representation number is at most 3.

## Body (paste into the MathDB body field)

Use the written proof in this folder: manuscript.pdf. The complete Lean source is in lean-packet.tar.gz.
