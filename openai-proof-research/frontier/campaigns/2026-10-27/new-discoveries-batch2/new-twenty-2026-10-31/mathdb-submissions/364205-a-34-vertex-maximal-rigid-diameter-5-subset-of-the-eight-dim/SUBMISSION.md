# MathDB 364205: A 34-vertex maximal rigid diameter-5 subset of the eight-dimensional Hamming cube

- Problem: https://mathdb.com/p/364205
- Source: Briggs-Feng-Wells, Facets in the Vietoris-Rips complexes of hypercubes, arXiv:2408.01288 v1/v2, Section 6 Conjecture 1; MathDB 364205
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `MathDB364205.literal_source_refutation : ¬ LiteralSourceClaim; MathDB364205.source_refutation`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `draft.pdf`
- Lean source: `source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded primary-body and registry comparison; not worldwide priority remaining_literature_limits: Original Kleitman 1966 / Ahlswede-Katona 1977 bodies read only via Bezrukov 1987 and Horlemann-Ravi 2026; Broad nonlinear-anticode and saturated-family literature not exhausted; No journal version or errata located; MathDB/Palomar inaccessible trust_limits: Prebuilt upstream Mathlib oleans trusted; no source-to-olean attestation; leanchecker shares the installation; Sampled private-RSS guard plus systemd MemoryMax not_claimed: Exact b'(8;5); Minimal counterexample; Classification, family or asymptotics; Worldwide priority; Publication or peer review
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Briggs-Feng-Wells conjecture that b'(n;r), the largest cardinality of an inclusion-maximal diameter-r subset of the n-cube, equals 2^r whenever n >= r. An explicit 34-point subset of the signed 8-cube has diameter exactly 5, is inclusion-maximal subject to diameter at most 5, and has a diameter partner at every point, so b'(8;5) >= 34 > 32 = 2^5. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Explicit 34-point subset of signed Q_8 with diameter exactly 5, inclusion-maximal subject to diameter <= 5, and a diameter partner at every point; hence b'(8;5) >= 34 > 32, refuting Briggs-Feng-Wells Conjecture 1 (b'(n;r)=2^r for n>=r).

## Body (paste into the MathDB body field)

Use the written proof in this folder: draft.pdf. The complete Lean source is in source-only.zip.
