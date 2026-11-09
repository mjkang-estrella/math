# Round 6: verified mask checker and heavy pilot, partial

The general bitmask RUP soundness theorem and literal-list encoding equivalence are proved. The optimized 1,000- and 5,000-step heavy pilots passed strict compiler and explicit-module leanchecker replay. No unconditional refutation or new closed normalized-CNF prefix is claimed. Root decides acceptance.

The 5,000-step pilot covers zero-based steps [13561,18561), 163,758 hint uses. Compiler: 115.66 s. Checker: 71.51 s. Combined: 187.17 s, 874.92 hints/s, 27.34 times round 5's stated approximately 32 hints/s. Peak RSS: 1,669,948 KiB. These timings include local checks and conditional mask entailments; they exclude the unimplemented concrete input encoding and dependency assembly. The overlapping 1,000-step results and ordinary-elaboration baseline are in results.json.

Endpoint in the fresh experimental packet: `Percolation.not_conjecture20_mask_conditional : NormalizedCNFUnsat5 → ¬ Conjecture20`. Its normalized-unsatisfiability premise remains unproved. NoMinimalTwoRound5 and Percolation.not_conjecture20_unconditional remain unproved.

The complete round 5 archive is preserved byte-identically as inherited.zip (SHA256 9add6cc761e26a70637ea9a8555199187c705f121a3a25b1159ce2f22ec7637c). Its 475 modules and conditional endpoint after 13,561 additions remain intact; exactly 116,110 suffix additions remain there. This round does not rebuild that entire inherited replay or claim to replace it. The smaller source-only.zip is a self-contained checker/pilot development packet, not a complete continuation certificate.

Fresh strict packet replay: **195/195 compiler passes and 195/195 explicit-module leanchecker passes**. Compiler wall total: **409.69 s**. Checker wall total: **209.76 s**. Combined successful final-packet replay: **619.45 s**. These are GNU per-process times, excluding development experiments, interrupted/omitted baseline modules, shell overhead and reporting. Source scan and local metadata audit passed. The endpoint and general checker use only propext, Classical.choice and Quot.sound.

The direct-expression builder removes most term elaboration overhead while constructing ordinary Eq.refl proofs checked by both kernels. The compiler checks each added declaration; leanchecker independently rechecks the serialized declarations. No native decision oracle is used.

Development failures and the externally interrupted large ordinary baseline are disclosed in REPRODUCE.md and full logs. No resource cap was raised. Final replay used safe extraction and rolling source/output stamps; the archive was updated with unchanged validated source bytes plus new modules, without copying compiled outputs. All final source bytes are compared with the extraction. No background worker remains at handback.

Files: source-only.zip; inherited.zip; SUMMARY.md; PROOF.md; STATEMENT-CORRESPONDENCE.md; REPRODUCE.md; NEXT.md; results.json; module-times.json; module-order.txt; progress.json; normalized-progress.json; axioms.txt; metadata-audit.txt; retained-source-comparison.json; inherited-source-comparison.json; certificate-sha256.txt; certificate-shrink-analysis.json; fresh-replay.log; fresh-extracted/logs/; packet/src/; raw.py; pilot.py; MaskBuild and MaskRUP sources.
