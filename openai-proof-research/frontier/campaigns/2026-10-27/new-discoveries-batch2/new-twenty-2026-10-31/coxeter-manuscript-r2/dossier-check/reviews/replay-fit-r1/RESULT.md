# Replay-fit handback: 324342 replay passed; 330264 blocked

Not acceptance. Credit is zero; root decides.

## 330264: whole-module preservation blocks restructuring

The canonical ZIP and extracted recorded manifest hashes match. Eight freshly compiled prerequisite modules passed explicit-module leanchecker. The unchanged SpectralWitness module hit wall 140 seconds, peak RSS 2,817,976 KiB. Endpoint compilation and fresh endpoint axiom/metadata checks were not reached.

The durable diagnostic entry markers show AP, AQ, A_pq, A_qp, A_intertwine, adjacency_charpoly, CP, CQ and C_pq were reached. Differences between entry timestamps give about 22.4 seconds for A_pq, 24.0 for A_qp and 59.8 for A_intertwine. The diagnostic was killed by signal 9 after 134 seconds, without an RSS or wall reason recorded; CPU-cap termination is plausible but not independently identified. No claim that any single declaration exceeds a cap is made. This points toward cumulative matrix-proof work in one module.

TASK.txt requires “Every module that holds definitions or the endpoint statement must stay BYTE-IDENTICAL”. SpectralWitness contains AP, AQ, CP, CQ, LP, LQ, edgeMapG/H, edgeEquivG/H and lineIsoG/H definitions, interleaved with proofs. It is not the endpoint module, so the endpoint-import exception does not apply. Splitting this module or replacing its proof bodies changes a definition-containing module. No such relaxation was assumed. All its bytes, and all other 330264 modules, remain unchanged. No replacement packet is claimed.

This is a preservation-rule blocker, not evidence that the mathematics inherently requires changing a definition. Allowing unchanged definition declaration text to move between files would enable a different task. The requested successful 330264 replay is NOT COMPLETE.

## 324342: endpoint import exception used

The frozen main, audit and control source hashes match r4/MANIFEST.json. The original main exceeds 6 GiB during import, before its first definition; an import-only diagnostic reproduces the failure. No individual candidate proof was reached in that baseline profile.

The endpoint module originally imports all of Mathlib. The explicit endpoint-import exception permits replacing that import. Its new imports are InformationTheory.Hamming, LinearAlgebra.Matrix.NonsingularInverse, LinearAlgebra.Dimension.Constructions, Data.ZMod.Basic, Tactic.NormNum and Tactic.NormNum.Prime. The entire body following the imports is BYTE-IDENTICAL, including every definition, proof and endpoint statement. No proof was moved, split or replaced. The supplied Audit and Controls files are byte-identical. MetadataAudit is new audit machinery, not part of the mathematical witness.

`324342-replay-fit-source.zip` is source-only. It was safely extracted to fresh-324342 without objects; all four modules were strictly compiled one per process and passed explicit-module leanchecker. Audit printed endpoint axioms; MetadataAudit checked all local main/control declarations for unsafe, partial, implemented_by, extern and _unsafe_rec flags/names and disallowed axioms, failing if found. The supplied Paley non-vacuity control was rebuilt. The endpoint and control use only propext, Classical.choice and Quot.sound. Full logs are under logs/final324342-*.

The first metadata audit attempt had a type-inference error in its counter variable. This was fixed with a Nat annotation, the source ZIP regenerated, and ALL four modules replayed from a new extraction. Preliminary logs remain clearly marked.

## Deliverables and integrity

- input-verification.json and 330264-manifest-verification.json: canonical packet bindings and hash checks.
- statement-preservation.json: file hashes, endpoint statement text/hash, unchanged 324342 body hashes and moved-proof list (empty).
- 324342-imports.diff: complete old/new main-module diff.
- 324342-replay-fit-source.zip and 324342-packet.sha256: successful source packet and digest.
- timings.tsv and per-candidate timing tables: watchdog wall/RSS results, including failed diagnostic calls.
- REPRODUCE.md, final324342.sh, package324342.py: resumable capped replay and safe extraction.

All Lean, checker and Python calls used the RSS watchdog, two-CPU affinity, CPU 120 seconds, wall 140 seconds, 6 GiB RSS and MALLOC_ARENA_MAX=2. All Lean calls used -M3500. Heavy processes were serial; no limit was raised. Temporary paths, caches, extracts and builds are lane-local. No candidate/review lane was written. No network, git, child agent, publication, upload, browser or external message was used. The initial buffered-marker diagnostic was manually stopped before replacement; it is not a resource failure. No candidate mathematical definition or statement was changed. Imported core/mathlib objects remain trusted.

At handback the process check found no running Lean, leanchecker or lane watchdog. The successful 324342 run's maximum build wall time was 30 seconds (MetadataAudit), maximum sampled RSS 2,932,156 KiB. Main-module build was 14 seconds / 2,833,112 KiB; main leanchecker was 15 seconds / 2,468,948 KiB. Metadata audit covered 116 local main/control declarations and reported zero forbidden metadata.
