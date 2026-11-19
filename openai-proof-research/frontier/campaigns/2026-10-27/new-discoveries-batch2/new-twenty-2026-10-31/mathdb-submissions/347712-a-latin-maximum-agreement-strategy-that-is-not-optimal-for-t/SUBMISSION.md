# MathDB 347712: A Latin maximum-agreement strategy that is not optimal for the finite field objective

- Problem: https://mathdb.com/p/347712
- Source: arXiv2008.11448v2 §7.2 Conjecture3 with Definition3; ICALP2021 Conjecture25; Published DOI10.1002/rsa.21114 Conjecture3 with Definition3
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `MathDB347712.source_refutation; LatinFidelity.restricted_refutation; LatinFidelity.ordinary_partition_counterexample`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `proof-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded primary-body and registry comparison, not worldwide priority certification remaining_literature_limits: Incomplete specialist and citing literature; Uninspected registry proof bodies and historical deletions; Live MathDB/Palomar inaccessible; Frozen lawful institutional publisher body, no fresh Wiley/complete erratum authentication trust_limits: External prebuilt package oleans trusted; No full upstream source-to-olean attestation not_claimed: Worst-target optimality refuted; Every interpretation of raw MathDB wording resolved; Exact optimum F(5); Smallest counterexample order; Necessity direction refuted; No optimal Latin strategy exists; Asymptotic improvement; Probability-space Lean theorem; Publication or journal peer review
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Latin-implies-optimal direction of the finite-field characterization conjecture of Czumaj, Kontogeorgiou and Paterson. For the exact finite-field objective with five symbols, the cyclic Latin square strategy attains field value 290 while an explicit Latin strategy reaches 302, both partitioning all 120 permutations into five nonempty fibres; the worst-target objective and the converse direction are not settled. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Refutes the universal Latin-implies-optimal direction of the source Definition3 finite field characterization: two nonempty Latin maximum-agreement partitions at n=5 have actual fields290<302. MathDB347712 is interpreted through its explicit source Definition3.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in proof-source.zip.
