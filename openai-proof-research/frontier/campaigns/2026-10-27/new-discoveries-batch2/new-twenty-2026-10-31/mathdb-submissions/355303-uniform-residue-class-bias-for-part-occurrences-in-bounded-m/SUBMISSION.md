# MathDB 355303: Uniform residue-class bias for part occurrences in bounded-multiplicity partitions

- Problem: https://mathdb.com/p/355303
- Source: Jackson–Otgonbayar arXiv2207.04352v1 Conjecture1.4
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `RB355303.original_weak; RB355303.original_strict; RBReplayAudit.conjecture_1_4`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `manuscript.md`
- Lean source: `proof-package.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. (no novelty limits stated in record)
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: both clauses of the conjecture of Jackson and Otgonbayar on occurrences in partitions with bounded multiplicity. For t >= 6 and 1 <= r < s <= t, the total number of occurrences of parts congruent to r modulo t, over all partitions of n in which no part appears k or more times, is at least the corresponding count for s when k >= 3, and strictly greater for k >= 2 whenever n > max(t+3,16). The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

For all t>=6 and1<=r<s<=t: D_k(r,t;n)>=D_k(s,t;n) for everyk>=3,n>=1; strictly greater for everyk>=2,n>max(t+3,16). Parts occur with multiplicity<k; occurrences counted with multiplicity; representative t means0.

## Body (paste into the MathDB body field)

Use the written proof in this folder: manuscript.md. The complete Lean source is in proof-package.zip.
