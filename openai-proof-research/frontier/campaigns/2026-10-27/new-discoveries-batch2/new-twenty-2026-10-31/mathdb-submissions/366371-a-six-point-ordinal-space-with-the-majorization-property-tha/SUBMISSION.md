# MathDB 366371: A six-point ordinal space with the majorization property that does not embed in the real line

- Problem: https://mathdb.com/p/366371
- Source: Keller-Petrov, Ordinal spaces, Acta Math. Hungar. 160 (2020) 119-152; arXiv:2412.17391v1 Conjecture 7.4; MathDB 366371
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `OrdinalSpaces366371.not_majorizationConjecture : ¬ MajorizationConjecture; OrdinalSpaces366371.witness`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `source-only-proof.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison (citing works Echeloned Spaces and Towards Ordinal Data Science read; classical scaling literature bounded); not worldwide priority remaining_literature_limits: Published 2020 Acta Math. Hungar. text not read (arXiv v1 Dec 2024 postdates it); Classical unidimensional scaling and absolute-difference literature not searched body by body; MathDB/Palomar inaccessible trust_limits: Prebuilt upstream Mathlib oleans trusted; no source-to-olean attestation; leanchecker shares the installation; Sampled private-RSS guard plus systemd MemoryMax not_claimed: Minimality; n=5 sufficiency; Classification; Worldwide priority; Publication or peer review
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Keller-Petrov Conjecture 7.4 in the range n > 5, beyond the cases where the source proves sufficiency, which reach only n <= 4. A six-point tie-free ordinal space has the majorization property of the source's Definition 7.1 for every chain length, with repeats and permutations admitted, yet admits no order embedding into the real line. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Six-point tie-free ordinal space whose identity enumeration has the Definition 7.1 majorization property for every chain length (repeats, permutations) but which admits no embedding in R; refutes Keller-Petrov Conjecture 7.4 in the range n>5 left open by the source (sufficiency proved only for n<=4).

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in source-only-proof.zip.
