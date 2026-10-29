# r4 handoff — incomplete; no acceptance or credit

The requested closed theorem `Polyomino57.UniversalContainer 11 Polyomino57.witness` is absent. So are unconditional `¬ Polyomino57.SourceFormula` and the source minimum-size upper bound. The certified complete chain remains through seven. This is not a completed assignment, and there is no demonstrated overall impossibility/resource blocker: flat arrays failed, but the balanced full size11 target tree succeeded.

## What can be reused

`formal/FamilyAssembly.lean` and `formal/FamilyTree.lean` remove global-array reduction from the semantic interface, reusing the frozen growth and normalization proofs. A local target array, checked successor row, and successful binary path/index for every local target suffice. A full such family chain plus terminal inclusions implies the literal UniversalContainer11 endpoint, with translation-only placements.

`tree/TreeBlock000.lean` through `TreeBlock066.lean` and `tree/TreeAll.lean` contain the entire generated size11 target family in 32-row leaves and 2048-row modules. All compiled sequentially; the combined import fits. These definitions do not assert connected-family coverage or forest correspondence. Their actual declarations are included in the final strict extracted audit.

`source-only-r4.zip` is the deterministic source-only component packet, SHA256 `ebef50b76b817c50d3416b16fda6fa0d7abb4aff801d364c23903d851cc6ba70`. `archive.json`, `modules.json` inside the archive, and `fresh-extracted/verification` identify the exact replay/audit scope. A separate repack reproduced identical bytes. No compiled artifacts are packaged.

## Data for all remaining rows, not proofs

`closure-path-data.zip` contains paths/indices/translations for ALL 49,841 source rows from sizes7,8,9,10, covering781,147 absent-neighbor edges. `closure-path-data-receipt.json` records per-stage hashes and counts. Each record gives the source-row index and each absent neighbor's target global index, translation, binary path and within-leaf index. Paths use the exact balanced construction in generate_tree.py (2048-row blocks, 32-row leaves). Only the size11 tree has been emitted/compiled as a complete tree; sizes8–10 still need their analogous common family definitions.

`terminal-map-data.zip` contains correspondence DATA for every generated terminal row to an actual frozen forest chunk (`TerminalNNNcK`), its within-chunk index, the raw-to-generated translation, and the induced generated-row placement. All135268 supplied rows were used exactly once by the data script. This does not establish a formal count, completeness, membership, or equality theorem. No such external count is a premise of the Lean interfaces.

Both data archives are explicitly DATA_ONLY_NOT_KERNEL_PROOF. Their scripts respect512MiBAS/CPU/wall bounds and can be rerun locally from immutable extracted inputs plus enumerate.py. They must be emitted into kernel-safe literal checks before adoption.

## Benchmark and unfinished work

Three global eight-row7→8 checks passed in10.32/15.19/29.99seconds, indicating costly global index traversal. Flat size10/11 target modules were killed at the RSS threshold. Balanced size11 target definitions and all12 local batches (8/32/128 rows at every remaining transition) passed. The largest local batch10→11 took36seconds and about2.20GiB. These are benchmarks, not all-row closure certificates. Detailed receipts are in benchmark-results.json; failed syntax/default-limit attempts are retained under failures/.

Still mandatory: kernel-certify every source row, prove every target's actual common-family membership/path, assemble exact layer links with the size7 endpoint, prove terminal TreeMember/index and translation/equality correspondence to the checked forests, freshly replay consumed terminal shards, and close the unconditional literal endpoint. Then root still owns manuscript, review and acceptance boundaries. Counts stay5additional/35total; worker credit0.

## Final fresh replay

PASS_COMPONENTS_ONLY:142 modules,8502 actual-origin declarations,897.65seconds, peak sampled groupRSS2,545,184,768bytes. Standard3 axioms only; all actual unsafe/axiom flags false. Every candidate dependency was rebuilt from the extracted source packet. See FINAL-REPLAY-RECEIPT.json and fresh-extracted/verification/declaration-inventory.json. All three immutable input archives rehashed unchanged after replay. FINAL-RECEIPT.json explicitly records objective_met=false and demonstrated_overall_blocker=false.

Failure-log precision: initial size8/9 diagnostic log files were overwritten by corrected retries; their failing sources, run receipts, and diagnostic descriptions remain. Initial local syntax-failure logs and generator are retained under failures/.
