# MathDB 342705: Caterpillar and balanced species tree growth-factor conjecture

- Problem: https://mathdb.com/p/342705
- Source: https://mathdb.com/p/342705/caterpillar-and-balanced-species-tree-growth-factor-conjectu; https://arxiv.org/abs/1905.04971v1; https://pmc.ncbi.nlm.nih.gov/articles/PMC7052048/
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `LiteralDL.FinalStage.source_target`, `LiteralDL.FinalStage.source_four_claims_expanded`, `LiteralDL.FinalStage.source_event_four_claims_expanded`, `LiteralDL.FinalStage.unranked_four_claims_expanded`, `IndependentReplay.actual_event_four_claims`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `FINAL-PAPER-v1.md`
- Lean source: `dl-history-accepted-proof-packet-20261115-v1.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Bounded SUBSTANTIAL: model-specific Catalan associator and strict log-conjugate convexity/expansion establish all-size threshold extrema with exact shape equality and uniform eventual counts, plus contrasting growth orders. The balanced source objective is not ordinary smallest-first Huffman (six equal leaves split3|3 rather than4|2); this blocks that direct specialization, not every unread merge theorem. All elementary growth steps alone would not establish substantiality. Inspected work yields no complete routine specialization or whole-target counterpart; specific unread merge-function risks remain explicit. No worldwide priority certificate. not_claimed: worldwideabsence; cleanprocess; linear asymptotic equivalent; caterpillar Theta(k^2); reading inaccessible protected bodies; audit upstream truth
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: all four claims of the growth-factor conjecture for the duplication-loss grammar on full binary species trees. One species-uniform cutoff makes the caterpillar the count maximum and the recursively leaf-balanced tree the count minimum, with equality exactly on the two isomorphism classes; growth factors exist, the caterpillar's ratio to the leaf count k grows without bound, and the balanced growth is Theta(k), between 2k and 1000k. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

For the source duplication-loss grammar on full binary unranked rooted species trees, with k>=1 species leaves and n extant gene leaves, prove all four claims of Conjecture4.1 (v1)/4.5 (final): one species-uniform eventual cutoff N_k makes caterpillar the count maximum and recursively leaf-balanced tree the count minimum, with equality exactly on their child-swap isomorphism classes; actual exponential growth factors exist, caterpillar growth/k tends to infinity, and balanced growth is Theta(k), explicitly 2k<=growth<=1000k for every positive k. Histories have ordered duplication, explicit speciation/loss, extant genes only at species leaves, no transfers/ranking/all-loss histories. Counts are literal finite source-event cardinalities, also transported to unranked species quotient. No asymptotic equivalent constant or caterpillar Theta(k^2) is asserted.

## Body (paste into the MathDB body field)

Use the written proof in this folder: FINAL-PAPER-v1.md. The complete Lean source is in dl-history-accepted-proof-packet-20261115-v1.zip.
