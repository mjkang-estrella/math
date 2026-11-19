# MathDB 364095: No four-label edge coloring of K5 distinguishes all triangles by color sets

- Problem: https://mathdb.com/p/364095
- Source: Pilsniak-Wozniak arXiv:2407.19050v1 Conjecture 5 p.4; MathDB 364095 The set-palette conjecture for complete graphs
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Palette.source_refutation : ¬ Palette.SourceClaim; Palette.no_four`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `source-only-proof.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded primary-body, registry and version comparison; not worldwide priority certification remaining_literature_limits: Bounded source/citing search; Semantic Scholar/Crossref rate-limited routes not retried; Current served arXiv v1 only; no publisher version located; Registry path screen plus selected bodies, not all-file semantic review trust_limits: External prebuilt upstream oleans trusted; no source-to-olean attestation; leanchecker shares the Lean installation; Sampled RSS caps are not transient-peak guarantees not_claimed: Exact tau_s(5); Smallest counterexample; Multiset conjecture refutation; Infinite family, asymptotics or corrected formula; Worldwide priority; Publication or peer review
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Pilsniak-Wozniak conjecture that tau_s(n) = n-1, at n = 5: every colouring of the edges of K_5 with four labels gives two distinct triangles with equal edge-colour sets, so no such colouring distinguishes all ten triangles. The multiset version, the same authors' Conjecture 4, is not touched. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Every map E(K5)->Fin 4 has two distinct triangles with equal edge-color sets; refutes Pilsniak-Wozniak arXiv:2407.19050v1 Conjecture 5 (tau_s(n)=n-1 for all n>=4) at n=5. Multiset Conjecture 4 untouched.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in source-only-proof.zip.
