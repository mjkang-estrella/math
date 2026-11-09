# Reproduction and trust boundary

This is an AI-assisted DRAFT, not acceptance. No Lean, lake or leanchecker was run in this lane. Root alone accepts; zero accepted credit.

## Deliverables

paper.md is the complete editable manuscript source. scripts/build_pdf.py converts its eight explicitly delimited pages through Pango/Cairo and Ghostscript. PROOF.md contains the mathematical argument separately. Fonts are bundled for repeatable glyph selection. The PDF is eight Letter pages. qa/ contains every final page rendered at 110 dpi; receipts/visual-qa.json binds their inspection to the PDF hash.

lean-source.zip is the BYTE-IDENTICAL round-7a packet, SHA-256 987233b0343fb9855f659eefedaf28bc2a91576cf5c6c3a50342671895d3d175. packet-extracted/ contains its verified bytes. No source was edited. Its 54 modules include the r4b arbitrary-tree bridge. sources/ contains frozen primary-source material, review evidence, round summaries/proof/correspondence/results, and the root ruling, with original paths and hashes in receipts/source-copies.json. The raw MathDB line is copied without parsing/reserializing; receipts/mathdb.json records its raw hash and inherited source. Review evidence/hash-chain.json and additional-input-before.json preserve the original chunk/line provenance.

## Lane-local commands

Run from this directory, with Python 3 and installed Pango, Cairo, Ghostscript and Poppler. No network or package installation is needed. The commands create only lane-local outputs. The wrapper sets two-CPU affinity, MALLOC_ARENA_MAX=2, CPU 120 seconds, wall under 140 seconds, address space at 5 GiB and sampled aggregate process-group RSS below 6 GiB. Use one command at a time:

    MALLOC_ARENA_MAX=2 python3 -I scripts/capped.py python3 -I scripts/verify.py
    MALLOC_ARENA_MAX=2 python3 -I scripts/capped.py python3 -I scripts/build_pdf.py
    MALLOC_ARENA_MAX=2 python3 -I scripts/capped.py pdftoppm -r 110 -png paper.pdf qa/page

verify.py checks safe relative ZIP paths, duplicate names, link/file types, per-file and total uncompressed size, absence of compiled Lean/shared-library payloads, every extracted member byte, 54 modules, source-copy hashes and the raw record. It directly transcribes the frozen label formula and checks 15 inherited parameter cases: t in {2,4,6}, n in {1,2,3,4,5}. Every label interval, adjacent weight comparison and exact colour count is checked. The two manuscript examples are recorded in full. Diagnostics are not proofs. This lane does not execute packet scripts. Re-rendering requires a new visual QA receipt; PDF metadata timestamps may change, so rebuilt PDFs are not promised byte-identical.

## Formal replay evidence, not a new replay

The inherited r7a and independent fidelity-review reports record strict fresh-extraction builds and explicit-module leanchecker runs for all 54 modules, allowed endpoint axioms propext/Classical.choice/Quot.sound, and source/metadata audits. The preliminary fidelity run with defective process-group monitoring is excluded. Consult copied review.json, REVIEW.md, evidence/source-scan.json, evidence/local-metadata.tsv and module-timing-rss.json. The packet's REPRODUCE.md and scripts pin Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and describe the original build environment. A future independent root replay needs those external read-only dependencies and separate authorization; it is not performed by the commands above. Parent final replay and registry-refresh receipts arrived during sealing, were hash-bound before reading, and are copied under sources/antimagic-parent-final-r1/. The root replay reports PASS (54 modules); the registry receipt reports CLEAN for its selected complete-tree path screen, not a full-body proof search.

## Integrity and limits

inputs-before.json and inputs-after.json bind the frozen files at their original absolute paths; receipts/input-integrity.json records equality. The supplemental Brondani-França body was first opened for author metadata immediately before hashing; this limited deviation is disclosed in supplemental-binding.json. It was never modified. Core specified input hashes preceded content review. The ZIP and payload manifests permit offline copy verification. manifest.sha256 covers deliverable files other than itself, archive hashes and the outer dossier ZIP; archive-sha256.json binds the latter and manifest. Scratch tmp/ is excluded from the deliverable ZIP. Original failed PDF-tool attempts remain in process receipts; the final successful Pango build and render supersede them.

Prior-art screens are bounded. Both closed-access leads remain UNREAD, and no priority claim is made. No publication, git, upload, external messaging, browser use, shared-ledger edit, other-lane write or child delegation occurred. The PDF skill's marker/default directories were not used because the user's lane-only restriction takes precedence. The default Python lacked reportlab; the available Pango/Cairo and Ghostscript tools were used offline instead.

## Round 2 correction and reproduction

Run all commands from this lane. The round-1 build script and frozen Lean ZIP remain unchanged. scripts/audit.py is the fresh transcription and comprehensive 20-case audit (t in {2,4,6,8}, n in {1,2,3,4,5}); it also applies the two manuscript corrections idempotently. Run:

    MALLOC_ARENA_MAX=2 python3 -I scripts/capped.py python3 -I scripts/audit.py
    MALLOC_ARENA_MAX=2 python3 -I scripts/capped.py python3 -I scripts/build_pdf.py
    MALLOC_ARENA_MAX=2 python3 -I scripts/capped.py pdftoppm -r 110 -png paper.pdf qa/page

Every new render requires new visual inspection and a new PDF-bound receipt. Numerical audits do not replace a proof. AUDIT.md identifies the additional depth-two H correction, the binary example correction, all statement groups, exact examples, and provenance limits.

For sealing, scripts/seal.py runs under scripts/capped.py. Its process receipt is redirected into excluded tmp/ by a small optional environment setting in the wrapper; the sealing script itself writes receipts/seal-process.json before manifest generation. It checks all bound inputs, builds manifest.sha256 and dossier.zip, safely extracts to tmp/dossier-fresh/, checks membership and every digest, and writes a detached receipts/dossier-verification.json. The outer archive-sha256.json binds the ZIP, manifest and verification receipt. Both detached files and the outer ZIP are excluded from the payload manifest to avoid circular hashes. tmp/ is excluded; all other deliverable files are covered.

inputs-before.json and inputs-after.json cover the complete round-1 lane files, its inherited bound inputs, the round-2 task, frozen packet and root example check. The task and two required references were necessarily read before the first hash, per the explicit instruction to read them before anything else. No changes to these inputs were made. Older round-1 integrity/visual/extraction receipts are preserved under receipts/inherited-r1. Its other process receipts remain historical evidence; current round-2 commands have later timestamped receipts. Acceptance remains solely with root and accepted credit is zero.
