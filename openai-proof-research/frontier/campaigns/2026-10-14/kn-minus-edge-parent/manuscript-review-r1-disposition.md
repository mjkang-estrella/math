# Parent disposition: manuscript audit round 1

**REVISE.** The delivered review requests no mathematical repair to Theorem A (every order n >= 2, every edge) or Corollary B (every m >= 4, every path of n >= 1 edges). Preserve both full statements. This is a manuscript revision gate, not acceptance; campaign remains **4/10**.

T3 reports the task as `interrupted`, with `result_available` and no pending child runs. Its terminal summary nevertheless delivers a substantive audit and external hashes. Parent authenticated those hashes and the complete delivered file inventory. Preserve the interrupted transport status; do not relabel the task completed. Unlike an unsealed partial draft, this delivered audit has a matching externally identified output manifest and review text.

The three required fixes agree with P1–P3 in the existing `manuscript-r1-disposition.json`:

1. **R1 — attribution.** The new minus-edge lower bound enters the product formula only for odd m >= 13 **and path length n >= 2**. At n = 1, the coefficient n−1 vanishes and the product equals 2 Z(m+1) using Harary–Hill alone. Retain the full corollary. Qualify the abstract, introduction, README, metadata and source map, extend the bounded-search limitation to the product, and credit the classical matching upper bound. At m=13 the values are 630 for n=1 and 1050 for n=2; the weaker order-15 counting ceiling would give 1049 in the latter case.
2. **R2 — formal coverage.** Replace stale claims that no lemma has been implemented or audited with the separate PASS_SCOPED_SUPPORT result: 47 support theorems and 17 definitions (64 declarations), 9 author controls and 16 independent controls. Preserve the paper-only status of the graph and drawing bridges, both evaluation injections, factor-of-four argument, even and upper arguments, full theorem and product corollary. U4 remains an explicit theorem hypothesis. No full crossing certificate is claimed.
3. **R3 — public verification.** Provide a public extraction mode based on `public-manifest.json`, without requiring the containing ZIP, private handoff manifest or SHA256SUMS. Keep full-directory verification, report missing files as verification failures, and test/document the clean-extraction route.

The independent reviewer reports a full proof reading, all 15 rendered pages, release checks R1–R9 with matching output, and no visual repair. The long modular diagnostic and Lean rebuild were not repeated by that reviewer. Parent read the complete audit and independently replayed its algebra checker after inspecting it; the output matches `independent algebra PASS`. Parent did not repeat the full manuscript audit, visual inspection or primary-literature search in this integration.

Authentication: 27 payload records plus output manifest and SHA256SUMS (29 review files), all 84 fixed inputs and all listed checksums match. All 113 protected files remained unchanged during parent verification. Paths are safe and unique; no symlinks or bytecode. The review manifest binds files, not directory membership; six directories were observed, including two empty ones. See `manuscript-review-r1-verification.json`.

Review SHA256: `caf0e282fa79dce82acdd12f8e188f1ab9f736d5a9024e729829bf63900f3df8`.
Output-manifest SHA256: `3298471988fcd7969840f3d11cb092b47b6fa61e3c5b9c752a5ed2b40f8f5b26`.

Next: a separate revised manuscript package addressing R1–R3, preserving the frozen r1 package and reviews, followed by focused revision checks. No manuscript bytes were changed, no new child launched, no acceptance or publication occurred in this integration. PCW and B8C remain separate.
