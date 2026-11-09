# Validation receipt, round 2A

The source-only archive is chord-source.zip, SHA-256 ecf5383aea8e309460520702f6bbbf87d6d85b774fddd36debd2434bfd7f80fa. It has 55 safe relative-path members and no object files. The required frozen input archive retains SHA-256 03971d4610581095feddea8040bd178f017d459794ac3e2374e73402d93ccbab.

Fresh extraction: fresh-extraction/. Every one of the 41 modules in modules.txt passed strict serial Lean compilation and a separate leanchecker invocation with an explicit module argument. The audit inspector also passed compilation and leanchecker. All 84 individual fresh replay logs have EXIT=0. Aggregate transcript: logs/fresh-rebuild.log. Per-module receipts: fresh-extraction/build/*.ok.

The final fresh audit log is fresh-extraction/logs/1793748529881179485.log. It records exact equality of the inventory and audited declaration sets: 266,049 declarations, including 449 LOCAL and 265,600 upstream declarations. All LOCAL unsafe, partial, axiom, _unsafe_rec, implemented_by, extern and unapproved transitive axiom counts are zero. Upstream implementation metadata are reported separately in results.json. The inspector reads opaque proof bodies with allowOpaque := true and includes generated declarations through module inventories. Its leanchecker receipt is fresh-extraction/logs/1793748559680554880.log.

The fresh audit's peak sampled RSS was 3,241,940 KiB, below the 6 GiB cap. Every heavy process used the required wrapper, two-CPU affinity, CPU/wall bounds and MALLOC_ARENA_MAX=2; every Lean call used -M3500. Heavy processes were serial within this lane.

The independent regression and all four negative controls passed: logs/1793748300959246016.log and regression.json. It checks 995,572 diagram/assignment pairs through five chords, with exact Euler parity and nonnegativity checks and equality of the two evaluators. Controls reject the wrong Euler offset, omission of an empty-circle term, uniqueness at four chords and the wrong representative. These are computational checks, not proofs of the open generic bridge.

All 33 inherited module hashes agree before and after (frozen-before.sha256 and frozen-after.sha256, cmp exit 0). logs/frozen-hash-check.log records all 33 checks. The results postprocessor checks equality between each submitted source and its freshly extracted source, each replay marker and its source hash, and each inherited source and the frozen extraction. Its receipt is logs/1793748564466343083.log.

No background lane process remains at handback. No acceptance is claimed. OrbitCounterCorrect and FacePermutationCorrect are the only unconditionally closed round-1 Props. EulerRealization and Heredity are proved from Deletion; DartBridge and Deletion remain open.
