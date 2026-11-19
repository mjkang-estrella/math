# MathDB 365710: Complete bipartite graphs maximise sigma_t-irregularity among connected triangle-free graphs

- Problem: https://mathdb.com/p/365710
- Source: Filipovski-Dimitrov-Knor-Skrekovski arXiv:2411.04881v1 Conjecture 24; Ars Math. Contemp. 26 (2026) #P4.01 Conjecture 6.1; MathDB 365710
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Sigma365710.extremal_completeBipartite; Sigma365710.attainer_classification; Sigma365710.mathdb_365710`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `source-only-proof.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison by root materiality ruling; two independent reviewers retained HOLD on unread bodies; not worldwide priority remaining_literature_limits: Bell 1992 body unread (403); restated as unrestricted by Zhou and Elphick-Wocjan; Reti 2019 and Dimitrov-Stevanovic 2023 origin bodies unread; Strict Zagreb-gap literature screen bounded, not exhaustive; MathDB/Palomar inaccessible trust_limits: Prebuilt upstream Mathlib oleans trusted; no source-to-olean attestation; leanchecker shares the installation; Sampled private-RSS guard plus systemd MemoryMax not_claimed: Novelty of the deficit identity; Which of floor/ceiling part sizes wins for each n; Worldwide priority; Publication or peer review
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: complete bipartite graphs maximize the sigma_t-irregularity among connected triangle-free graphs. For every n >= 2 and every maximizer a of a(n-a)(n-2a)^2 over 1 <= a < n, the graph K_(a,n-a) is connected, triangle-free, and has sigma_t at least that of every connected triangle-free graph on n vertices; every graph attaining the maximum is complete bipartite with nonempty parts. This proves the source conjecture in full. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

For every n>=2 and every maximiser a of a(n-a)(n-2a)^2 over 1<=a<n, K_{a,n-a} is connected, triangle-free and has sigma_t at least that of every connected triangle-free graph on n vertices; every attainer is complete bipartite with nonempty parts. Proves arXiv:2411.04881v1 Conjecture 24 / Ars Math. Contemp. 26 (2026) Conjecture 6.1 in full.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in source-only-proof.zip.
