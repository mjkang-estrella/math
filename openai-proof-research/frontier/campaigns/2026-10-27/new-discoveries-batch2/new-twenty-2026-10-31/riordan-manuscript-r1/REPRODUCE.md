# Reproduction - DRAFT MathDB 338258

Root alone decides acceptance. No Lean, lake or leanchecker was run by this manuscript lane.

## Delivered files

- paper.md is the eight-page manuscript source; scripts/render.py produces paper.pdf.
- PROOF.md gives the mathematics and evidence account; STATEMENT-CORRESPONDENCE.md covers both endpoints.
- mathdb-338258.raw.jsonl is the byte-exact input record, including its final newline; RAW-RECORD.json records its hash.
- sources/ contains primary bodies and original retrieval receipts. reviews/ contains the independent review, its scripts, numerical certificates, searches and source receipts.
- evidence/ contains the discovery materials, formal-r2 reports, scripts/logs, root ruling, final replay report and registry refresh. Receipts preserve original paths and URLs, which are provenance, not paths within this package.
- 338258-infinite-family-source.zip is reused byte-identically. Its SHA-256 is 27175a85484d563031a12665736dbd4277de327cb726e1b6791d07a348c2c063. It contains 22 flat Lean source files, no compiled payload or internal manifest. safe-extraction.json supplies the external per-module manifest.
- riordan-full-dossier.zip contains every file enumerated by DOSSIER-MANIFEST.json and that manifest. DELIVERY-SHA256.json hashes both ZIPs and principal deliverables.

## Manuscript checks (no prover)

From this lane, choose unused log tags because the runner deliberately refuses log overwrite:

    python3 -I scripts/limited.py archive-repeat /usr/bin/python3 -I scripts/check_archive.py
    python3 -I scripts/limited.py math-repeat /usr/bin/python3 -I scripts/check_math.py
    python3 -I scripts/limited.py pdf-repeat /usr/bin/python3 -I scripts/render.py
    python3 -I scripts/limited.py png-repeat /usr/bin/pdftoppm -r 115 -png paper.pdf qa/page

The copied ReportLab 5.1.0 dependency tree in tmp/pdf-deps and fonts/ permit offline PDF generation with the recorded system Python environment. Poppler supplies pdftoppm and pdftotext. dependency-inputs-before.json and dependency-inputs-after.json pin the copied rendering inputs. Source code explicitly inserts only the lane-local dependency path. All output and temporary paths stay in this lane. The final page PNGs and qa/receipt.json document inspection of every page.

The runner limits affinity to at most two CPUs (one inherited CPU in this execution), CPU to 120 seconds, wall to 140 seconds, address space to 6 GiB, and samples child RSS against 6 GiB. MALLOC_ARENA_MAX=2. Only one heavy process runs at a time. Sampling is not a cgroup RSS guarantee. The first runner launch tried to raise an inherited address-space hard cap and failed in preexec before running the math script; logs/setup-failure.json records the correction. Later logged checks pass. No background jobs remain.

## Formal replay (root's separate responsibility)

Do not execute a prover as part of manuscript reproduction in this lane. To reproduce the formal certificate in a separately authorized root replay directory, place the exact ZIP at the replay root, copy evidence/formal-r2/scripts to its scripts directory, and create logs/ there. Use the supplied serial replay driver according to evidence/formal-r2-REPRODUCE.md. That driver invokes Lean and leanchecker and needs its pinned installation/cache paths. It extracts a new source tree and builds 20 proof modules and two audit-tooling modules. Its virtual-memory policy differs from this manuscript runner to accommodate mapped Lean caches.

Pinned Lean: 4.34.1. Pinned mathlib: d13f23b723b8a846827a245b89c10fc7d3f11612. Binary and lake-manifest digests are in evidence/formal-r2-results.json. Read-only prebuilt mathlib artifacts and the installed kernel/checker are trusted. The permitted axiom union is propext, Classical.choice, Quot.sound. Three deliberately false controls must fail; their sources are in evidence/formal-r2/scripts and excluded from the successful proof ZIP.

Root's evidence/replay-result.json records PASS for 22 strict builds and 22 checker checks of the exact packet. evidence/registry-refresh.json records the bounded registry screen. Neither report constitutes manuscript acceptance.

## Integrity and package convention

inputs-before.json and inputs-after.json hash every frozen file in the three input lanes, plus the task, model scripts and root reports used. Supplementary rendering inputs are separately bound. Frozen original files are never modified. input-integrity.json records the comparisons. Copies of Lean sources are verified against the frozen formal-r2 sources. RAW-RECORD.json verifies the exact raw-record copy.

DOSSIER-MANIFEST.json omits itself, the outer ZIP, DELIVERY-SHA256.json, package-validation.json and the packaging job's own log/receipt to avoid circular hashes. It includes every other dossier file, including lane-local rendering dependencies; no upstream build cache is bundled. The outer ZIP carries exactly that manifest and its enumerated members. package-validation.json independently checks all ZIP members against the manifest. Post-packaging receipts sit beside the ZIP and are outside its closure. DELIVERY-SHA256.json is the final external digest receipt.
