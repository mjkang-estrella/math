# Reproduction and evidence boundary

AI-assisted draft, zero credit. Root alone reviews and accepts. Campaign context 35/40 beyond 39, as supplied; no shared count is changed.

## Integrity and extraction without Lean

Verify dossier-manifest.json using `python3 -I verify_dossier.py` from the extracted dossier. Compare archive-receipt.json, delivered beside dossier.zip, to the downloaded ZIP hash. A manifest does not authenticate an untrusted distribution.

The current packet is frozen/330264-replay-fit-r2-source.zip, SHA256 00c3713935d6a13f701cd3a26f9c7f1a86633e0eb60ff00a7ed0d100ea3d2fb5. It has exactly 64 regular, single-component .lean paths and no compiled objects. proof/ is a safely extracted byte-identical copy. packet-manifest.json binds every module; safe-extraction-receipt.json records the test and historical Endpoint/GroupSemantics comparisons. No archive code was executed. `python3 -I run-capped.py corroboration python3 -I independent-corroboration.py` independently checks arithmetic with standard-library exact fractions, no third-party dependency.

The 2cab69a4914f29fb3f934b8f57c8807bcb3298bea7e1b535246e9e205e3acaab archive is historical provenance only; its original replay limits exceed this task's caps. Its historical receipts and all preserved review files are evidence of those earlier runs, not instructions or claims of new r2 execution.

## Optional independently authorized strict replay

This task explicitly prohibited executing Lean, lake or leanchecker; none was run here. For a separately authorized future replay in a writable extracted dossier, `python3 -I replay-current.py` builds one module per capped process, then explicitly checks it, following reviews/replay-fit-r2/modules.txt. The driver creates only lane-local build and log directories and stops on failure. Do not run concurrently or over an existing build. It verifies all source hashes first. Review the driver before use. The packet itself is never modified. The original replay-fit-r2 scripts are preserved unchanged as historical evidence under reviews/; notably their run script has an absolute path to its original lane and must NOT be executed from this dossier.

Pinned installed dependencies, not vendored in this dossier:
- Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin.
- mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and packages at /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages.
- sources/dependency-hashes.json is the historical anchored dependency manifest for 3,097 external source/olean pairs. Local spectral modules have since been split. No external cache rebuild or fresh external hash audit is claimed here.

StatementClosure computes the packet constants reachable from the endpoint type, transitively through types and bodies, including opaque/theorem bodies; the endpoint is included without seeding traversal with its proof. It prints endpoint axioms and rejects forbidden local metadata. Every generated local declaration must pass; endpoint axioms must be exactly propext, Classical.choice, Quot.sound. The preservation evidence was generated against the restructured compiled endpoint because the original SpectralWitness exceeded the wall cap. Reproducing the original comparison needs the historical archive and adapting preservation.py in a separate authorized copy. Both statement-closure modules remain wholly byte-identical, checked here without Lean.

Imported mathlib/core/package oleans remain trusted: matching source/olean hashes does not prove source-to-object provenance. Init, runtime and plugin sidecars use the installed toolchain assumption. This is not a portable vendored build or a full dependency rebuild. All original prior-art searches are bounded and dated; the journal version-of-record body remains unread. See paper section 5, reviews/ and parent-final-status.json. No fresh network screening was performed here.

## PDF and packaging

The manuscript uses the copied r1 Tectonic 0.17.0 binary/cache entirely inside this lane. Run `python3 -I run-capped.py build tools/tectonic --only-cached --untrusted --keep-logs paper.tex`. Compiler and TeX caches are excluded from the dossier; ordinary LaTeX with the listed packages also suffices. Render using `python3 -I run-capped.py render pdftoppm -scale-to 1400 -png paper.pdf render/page`. Every final paper page was visually inspected; pdf-qa.json binds the images to the final PDF. Source PDFs are unchanged reference evidence, not newly authored deliverables.

All writes and temporary/cache paths are lane-local. run-capped.py restricts affinity to two allowed CPUs, CPU 120 s, wall watchdog 138 s (<140), aggregate sampled RSS <6 GiB and address space <=6 GiB, MALLOC_ARENA_MAX=2. One heavy process runs at a time. Receipts preserve failed preliminary diagnostics as well as final passes. Initial input hashing followed the required introductory TASK/PDF/AGENTS/skill reads; it preceded copying and authoring. Parent-final is an active external lane: changes in its transient logs/build files are separately reported, not attributed to this worker. No git, network, child agent, upload, publication, external message or shared ledger edit occurred.
