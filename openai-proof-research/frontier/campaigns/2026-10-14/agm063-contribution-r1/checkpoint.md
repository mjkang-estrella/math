# AGM063 contribution review r1: checkpoint

**Status: COMPLETE. Verdict SUBSTANTIAL (moderate strength) for the full unchanged AGM063 target, conditional on the separate proof gate (R1).** No acceptance, count change (the ledger stays at 11/20 after R033; target 20; uploads stopped), Lean or full-formal claim, manuscript gate or publication. The parent alone integrates.

- **Role.** Independent substantial-contribution and eligibility gate. The reviewer is not an AGM063 author. No nested agents, git, staging or shared-index edits were used. Only this directory was written. The frozen author packet fresh-arithmetic-discovery-r18 is unchanged, and the identity checks confirm it.
- **Author anchors (external, caller-supplied):**
  - manifest 9afeca9bf3d6c272d7013e48c62e53ae92b1b1d4ccd3f52adcd9f35375cbb786
  - proof 285f584005acf9c5ed3fbaf9c6bd3ef320eecaf88df21ca22bace3ee7d971c8c
  - scope 03a4861c0ebd9ae1951bc3650d17d004f53e46303f3074425bb7e19d05677081
  - checkpoint 3c7d6197a9ceebc3d994359fccf1d49d2ec176865b0ec03dee71f2556eb7be6f
  - author verify.py c9eb4a5da90d7da24e998639a7fbb86cbafeb3608a42ac99bbaddc93f22fe814
- **Basis (review.md §§2–4).**
  - S1 plus Fujita's numerical toolkit (Lemma 3.6/3.7, Prop. 3.3, Thm. 3.4) does not supply the unsplit premise of Cor. 6.4: a split family gives only k≤r−1, which is no contradiction.
  - The new chain is three steps: (a) take the support dimension of the composed virtual correspondence, ≥2n−1; (b) use the two-endpoint saturated quotient and the fiber-divisor argument to get rc(V)-connectedness; (c) a bounded-degree dominating horizontal competitor bounds every family in Constr. 3.5. Neither the source nor Fujita contains this chain, and it is nonroutine.
  - Step (c) alone, and the final Fujita induction, the degree<2i unsplit argument, the rank-one case and the invariant checks are TECHNICAL or credited.
- **Required issues.** R1 conditionality on the proof gate; R2 exact attribution, including the dependence on S2; R3 the parametrised-to-actual equivalence for any Fujita-conjecture claim; R4 reading Watanabe's special-range papers before any novelty sentence.
- **Optional issues.** O1–O6. O5 is the stale "10/20" in the frozen author checkpoint.
- **Apparent mathematical issues.** None found at contribution-reading depth. This is not a proof verdict.
- **Identity.**
  - The author verifier positive run passes: 44 files, 13 directories, 9 blobs, 2 PDFs, 20 contexts.
  - The context tree and pin copies are byte-equal to repository sources/.
  - Fresh downloads of both primary PDFs byte-match the receipts.
  - This review's verify.py takes five caller-supplied anchors: --manifest-sha256 for this review's manifest.json, and --author-{manifest,proof,scope,checkpoint}-sha256.
  - Controls: one positive run and five single-wrong-anchor runs. Their transcripts are in controls/, exempt from the manifest by exact name and unbound.
  - Hashes and finite checks are not mathematics.
