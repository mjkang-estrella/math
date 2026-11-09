# Reproduce the draft dossier

All commands below are run from this lane. No Lean, lake, or leanchecker was run here. Root's decisive replay is pending, and zero accepted credit is assigned.

## Bytes and extraction
schrijver-source-r5.zip is copied byte-identically from the r5 lane:
SHA-256 685b78855d145dae95ba175796528739f8a9ee5ea54fb621fc78b5ccdc763d1b.
safe-extraction.json records path/link/object checks, every member hash, 474 Lean modules, and verification of the packet SOURCE-MANIFEST. proof-packet-safe is a nonexecuted extraction; its historical TASK.txt is not an instruction to this lane.

The raw record mathdb-352827.raw.jsonl includes its terminating newline and has SHA-256 b5f22645d8c39a7b9b81ebb016b3fa3bbc79b47330eea97cfb10693e12468a15. Original provenance: mathdb-normalized-chunk-0008.jsonl, one-based line 2143; immediate copied input: expanded-corpus-r122/raw/352827.jsonl.

## Ordinary verification
Use a fresh receipt tag if rerunning:
MALLOC_ARENA_MAX=2 taskset -c 0,1 timeout 140s python3 -I scripts/capped.py verify-new python3 -I scripts/verify.py

This regenerates complete stable-mask sets and all literal adjacency for the five stated graphs, verifies every retained representative BFS recurrence and rotation coverage, checks the explicit main pair/path and correction balls, and performs safe extraction without running archived scripts. Results are certificate-verification.json and safe-extraction.json.

## PDF generation
paper.md is the editable source; scripts/render.py is adapted from the hash-bound pdtar manuscript renderer. ReportLab is required. A locally copied, hash-bound package cache is in tmp/pdf-deps for this lane; it is excluded from the ZIP. An installed ReportLab distribution works too. Fonts are supplied with the dossier; no packages were installed or fetched.

MALLOC_ARENA_MAX=2 taskset -c 0,1 timeout 140s python3 -I scripts/capped.py render-new python3 -I scripts/render.py
MALLOC_ARENA_MAX=2 taskset -c 0,1 timeout 140s python3 -I scripts/capped.py raster-new pdftoppm -r 110 -png paper.pdf qa/new-page

Inspect every newly rendered page after an edit. qa/receipt.json applies only to the delivered PDF hash and final-page images. scripts/capped.py applies two-CPU affinity, CPU 120 seconds, wall 140 seconds, 6 GiB address-space limit (stronger than the requested RSS ceiling for these small processes), sampled child RSS, MALLOC_ARENA_MAX=2 and lane-local caches/temp paths. Run heavy steps serially.

## Formal replay reserved to root
Do not infer formal success from the ordinary checker. The pinned packet's REPRODUCE.md documents Lean 4.34.1, mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612, strict serial compilation, leanchecker and seven negative controls. Its replay entry point is scripts/replay.py --resume after fresh extraction. That command is documentation only here; root owns the decisive extracted replay in schrijver-parent-final-r1. Prior author replay and reviewer spot replay remain separate evidence.

## Packaging and limits
scripts/package.py verifies frozen input hashes, creates DOSSIER-MANIFEST.json, builds schrijver-full-dossier.zip, and checks its member bytes. It excludes tmp, redundant proof-packet-safe, initial QA images, and the outer ZIP. DELIVERY-SHA256.json, outside the ZIP, binds the ZIPs, manuscript and manifests without circular self-hashes. No source packet member is edited.

Initial brief/policy/report/inventory reads were not all capped and preceded hash binding. The before manifest was established before artifact copying/production and compared at handback. This procedural exception is disclosed in operations.json; it is not retroactively claimed compliant. The initial verify.py creation had a shell quoting failure; it was replaced before any verification succeeded. Root alone decides acceptance. No forbidden tools or external actions occurred.
