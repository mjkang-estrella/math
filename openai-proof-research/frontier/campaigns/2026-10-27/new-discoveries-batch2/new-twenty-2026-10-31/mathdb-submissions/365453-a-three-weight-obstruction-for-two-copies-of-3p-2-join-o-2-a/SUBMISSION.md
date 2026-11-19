# MathDB 365453: A three-weight obstruction for two copies of 3P_2 join O_2: a counterexample to Lau-Shiu Conjecture 4.1 on local antimagic chromatic numbers (arXiv:2410.17674; Utilitas Math. 124 (2025))

- Problem: https://mathdb.com/p/365453
- Source: Lau-Shiu arXiv:2410.17674v1 Conjecture 4.1 (Utilitas Math. 124 (2025) 189-206); MathDB 365453
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `not_conjecture41 : ¬ Conjecture41, where Conjecture41 := ∀ r s m : ℕ, 1 ≤ r → 1 ≤ s → 2 ≤ m → Antimagic.chiLA (LauShiu.graph r s m) = 3; LauShiu.graph r s m is the SimpleGraph 2r((2s+1)P_2 join O_m) and chiLA is the least colour count of local antimagic labellings (edge bijections onto 1..|E| with distinct weights on adjacent vertices), the definitions reused byte-identically from the accepted 354228 packet`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: bounded citing-work screens (OpenAlex coverage incomplete); Google Scholar and MathSciNet not consulted trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; the audit covers the packet's local declarations (axioms and metadata), not a full upstream closure inventory; chi_la = 4 is ordinary supporting mathematics, not a Lean claim not_claimed: chi_la(2(3P_2 join O_2)) = 4 as a Lean theorem; Any other parameter case; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Lau-Shiu Conjecture 4.1 that the local antimagic chromatic number of the duplicated join graph 2r((2s+1)P_2 join O_m) equals 3 for r, s >= 1 and m >= 2. At r = s = 1, m = 2, the 16-vertex graph admits no local antimagic labelling with three or fewer distinct vertex weights, and an explicit labelling with four weights shows its value is 4. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Lau-Shiu Conjecture 4.1: chi_la(2r((2s+1)P_2 join O_m)) = 3 for r, s >= 1 and m >= 2. False at r = s = 1, m = 2: the 16-vertex graph 2(3P_2 join O_2) has no local antimagic labelling with at most three weights (and chi_la = 4 by an explicit labelling, supporting).

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in source-only.zip.
