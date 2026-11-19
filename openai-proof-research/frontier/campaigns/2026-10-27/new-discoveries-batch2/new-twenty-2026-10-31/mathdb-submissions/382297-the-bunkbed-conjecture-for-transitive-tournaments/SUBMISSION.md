# MathDB 382297: The bunkbed conjecture for transitive tournaments

- Problem: https://mathdb.com/p/382297
- Source: MathDB382297; Hollom arXiv 2406.01790 Definitions 1.1-1.4, Model 4.5, Conjecture 6.4; European Journal of Combinatorics 128 (2025) 104188, model D7
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Bun.bunkbed_E7_transitive`, `Bun.prob_layer_true_le_false`, `Bun.card_token`, `Bun.card_out`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `bunkbed-transitive-tournaments.pdf`, `bunkbed-transitive-tournaments.roff`
- Lean source: `bunkbed-382297-source-only.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded source-primary investigation, not worldwide priority certification. prior_limits: The final journal version of Przybylowski, DOI 10.1016/j.ejc.2025.104289, is closed and unread; the supplied arXiv v2 is not final-equivalence evidence. Registry roots closed. Four searches in total across two reviews found no proof or disproof. trust_limits: Upstream Lean, mathlib and their oleans are trusted through pins and were not rebuilt. Reviewers are AI systems, not human referees. The relabeling of an abstract transitive tournament to Fin n is not formalized and is trivial. not_claimed: Worldwide novelty or publication priority; Human peer review; Separate credit for the column-homogeneous extension; Any statement for general acyclic digraphs
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved. For every n and all vertices u, v of the transitive tournament bunkbed, the number of token outcomes in which the lower copy of u reaches the upper copy of v is at most the number in which it reaches the lower copy of v, with one independent fair token per arc per layer and one shared bidirectional vertical token per index: the bunkbed inequality holds in this directed model. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

For every n and all u,v : Fin n, the number of outcomes on the n*n tokens of the transitive tournament T_n bunkbed in which (u,false) reaches (v,true) is at most the number in which it reaches (v,false). One independent fair horizontal token per arc per layer, one shared bidirectional vertical token per index, reachability as reflexive transitive closure, fixed endpoints.

## Body (paste into the MathDB body field)

Use the written proof in this folder: bunkbed-transitive-tournaments.pdf. The complete Lean source is in bunkbed-382297-source-only.zip.
