# MathDB 355140: A seven-vertex counterexample to the minimum-degree bound for Staller fast Maker-Breaker domination

- Problem: https://mathdb.com/p/355140
- Source: Bujtas-Dokyeesun arXiv2206.12812v1 Sections1.2-1.3 andConjecture7.2; Discrete Applied Mathematics344(2024)10-22 DOI10.1016/j.dam.2023.11.015 Conjecture7.2(i)
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `MathDB355140.winning_number_four; MathDB355140.source_refutation; Review.number_le_iff`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `355140-proof-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded primary-body, registry and historical comparison, not worldwide priority certification remaining_literature_limits: Uninspected specialist/citing bodies and thesis details; No all-registry-proof or deleted-history clearance; Live MathDB/Palomar inaccessible; No exhaustive publisher correction search trust_limits: External prebuilt upstream oleans trusted; no full source-to-olean correspondence attestation; Module leanchecker uses same Lean kernel, not independent foundation; Sampled RSS caps are not aggregate cgroup or transientpeak guarantees not_claimed: Separate Conjecture7.2(ii) refutation; Smallest counterexample; Infinite family or asymptotic/general bound; Worldwide priority; Publication or journal peer review
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the minimum-degree bound in Conjecture 7.2(i) on Staller-start Maker-Breaker domination games. The seven-vertex connected bipartite theta graph with branch lengths 2, 2 and 4 has minimum degree 2, and the optimal Staller-start game lasts 4 moves, exceeding the conjectured ceiling of 7/2, minus 2, plus 1, namely 3. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Sevenvertex simple connected bipartite theta with branchlengths2,2,4 has minimumdegree2 and Staller-start optimalwinningnumber4>ceil(7/2)-2+1=3. Refutes Conjecture7.2(i) and thus MathDB355140 conjunction.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in 355140-proof-source.zip.
