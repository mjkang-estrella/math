# Reproduction and artifact map

DRAFT, AI-assisted; zero accepted credit. All paths below are relative to this dossier. Work in an isolated writable copy under an authorized directory. This lane executed no Lean, lake or leanchecker and made no network requests.

- paper.md is the complete editable prose source, with explicit page divisions. scripts/build.py converts it to the portable flat OpenDocument source paper.fodt. paper.pdf is the eight-page exported draft. LibreOffice 26.8.2.2 was used because reportlab is not installed; the failed import receipt is preserved. No dependencies were installed.
- Rebuild source: `python3 scripts/run.py build-source python3 -I scripts/build.py`.
- Export: `python3 scripts/run.py render libreoffice -env:UserInstallation=file:///ABSOLUTE/AUTHORIZED/DOSSIER/cache/lo --headless --convert-to pdf --outdir . paper.fodt`. Replace the profile URL with a path within your authorized copy. No browser or server is required. Font: installed Noto Serif. LibreOffice may embed timestamps; reproduced PDFs need not have identical bytes.
- Render: `python3 scripts/run.py qa pdftoppm -scale-to 1250 -png paper.pdf qa/page`. Inspect every page. qa/ contains all final page PNGs and text extraction; receipts/pdf-qa.json binds the inspected final PDF and images.
- PROOF.md restates the proofs and scope; gate-E.md maps all eight fidelity conditions.
- mathdb-355217.jsonl is the exact cached raw line, including its terminal newline; mathdb-355217.sha256 binds its bytes. Do not treat its historical open status as present-day novelty evidence.
- evidence/ retains byte-identical read-only copies under original lane names, including source PDFs/text/receipts, mathematical/fidelity reviews, formal audit and results, root ruling, root replay and registry refresh. receipts/copied-inputs.json maps originals to copies and hashes. Historical obsolete discovery draft descriptions are provenance, not the current formal status.
- scripts/collect.py documents collection from the original sibling lanes; it requires that original layout. It was run once. No shared ledger is included or changed.

## Safe packet verification without Lean

middle-source.zip must have SHA-256 5a3e8ac8153651c55942d8f1288b50dd0c578b089c02d01c353b750b2c5bb62b. It is reused byte-identically. scripts/check.py rejects absolute paths, parent traversal, backslashes, duplicate names and symlinks, extracts into a newly created safe-extraction/, and compares every member byte-for-byte. It then independently builds G8 and its literal middle graph and enumerates subsets through the first feasible cardinality under both conventions. Run `python3 scripts/run.py checks python3 -I scripts/check.py` in a fresh copy without safe-extraction/. It deliberately refuses an existing extraction directory. No archive script is executed. Receipts record all 18 members, graph sizes, values and minimizing sets.

## Historical Lean replay (not run in this lane)

The archive contains the authentic source and its scripts. See evidence/middle-formal-r1/REPRODUCE.md for the original exact local dependency paths and replay command. Lean is 4.34.1; mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612. Replay requires those already installed read-only dependencies; this is not a hermetic dependency distribution. Compile serially with -j1 -M3500 -DwarningAsError=true and explicit-module leanchecker for MiddleBase, MiddleSmall, MiddleWitness, MiddleFinal and MiddleAudit. The root receipt evidence/middle-parent-final-r1/replay-result.json reports all passes, three expected negative failures, regression and allowed axioms. Fidelity review logs are independent bounded checks. Neither receipt rebuilds upstream mathlib from source.

## Reproducing the classification (not rerun here)

Read evidence/middle-review-r1/scripts/{gen.py,search.py,crosscheck.py,mocd.py} and their scripts/run.sh. Original commands and outcomes are retained in evidence/middle-review-r1/logs/. Class representatives are data/all1.txt through all8.txt. The review scripts resolve data paths against their lane, so use a fresh writable copy of that subtree and preserve originals. The discovery generator is evidence/expanded-corpus-r139/scripts/graphgen.py; its witness scripts are in work355217/. Family and characterization are proved in the paper; classification is computation only.

## Integrity and resource limits

frozen-inputs-before.json and frozen-inputs-after.json bind every file recursively in the five input lanes plus the root ruling. receipts/frozen-inputs.json reports byte identity. MANIFEST.sha256 and MANIFEST.json bind every distributed payload file; they exclude themselves and the archive checksum files to avoid self-reference. Cache/profile/tmp files and safe-extraction/ duplicates are intentionally omitted from the full-dossier ZIP; the extraction receipt and original source ZIP are included. The packaging supervisor receipt is written after packaging and is a sidecar; it and ARCHIVES.sha256 are outside the payload manifest. The ZIP's member list and byte hashes are checked against the manifest before completion.

scripts/run.py enforces two available CPUs, per-process CPU 120 s, wall 140 s, sampled process-group RSS 6 GiB, MALLOC_ARENA_MAX=2 and lane-local temporary/cache directories. Heavy operations run serially and are waited on. Shell setup and read-only inspection are lightweight. receipts/ includes successful and failed attempts; fonts.json records a failed isolated reportlab import. No jobs remain at handback. No acceptance is implied by a passed integrity check.
