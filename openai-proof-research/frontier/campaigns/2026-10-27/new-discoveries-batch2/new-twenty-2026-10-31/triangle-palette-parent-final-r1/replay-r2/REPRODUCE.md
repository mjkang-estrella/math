# DRAFT reproduction dossier — MathDB 364095

Zero accepted credit. Root alone accepts; 4/20 beyond 39 unchanged.

## External dependencies

Python 3 standard library for proof replay. Linux /proc, resource limits and CPU affinity are used. Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 with its pinned dependencies and built upstream oleans are required externally. pins.json includes the complete dependency manifest and binary hashes. No download, cache repair or upstream rebuild is performed. The mathematical source package is self-contained relative to those dependencies; it is not a standalone toolchain.

## Fresh extraction and replay

Choose a new empty writable directory. Do not reuse an author directory. All archive members are relative regular files; safe_extract.py rejects traversal and symlinks and creates a new destination. It never deletes files.

```sh
python3 safe_extract.py source-only-proof.zip /absolute/path/to/new-extraction
export LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
export LEAN_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
cd /absolute/path/to/new-extraction
python3 replay.py
python3 diagnostic.py
```

These are example dependency paths, not a required working directory. Override LEAN_BIN and LEAN_PACKAGES for another installation of the pinned bytes. HOME is retained from the actual environment. The driver excludes inherited Lean settings and author-local imports. It builds four source modules with -j1 -DwarningAsError=true, runs four leanchecker checks, audits all 66 declarations by module origin, full types, opaque-body presence via value? true, safe/nonpartial status and transitive axioms, and runs sanity examples. The only allowed axioms are propext, Classical.choice, Quot.sound. Three negative controls must fail with exit 1; the malformed certificate tests only invalid-header rejection. All output, commands, minimal environments, CPU selection, limits, exits, elapsed and sampled RSS go into replay-receipts/. The script refuses existing mathematical oleans. To repeat, use another fresh extraction: no cleanup command touches any author file.

Every call has CPU120s, wall140s, <=2 CPUs, 6GiB sampled process-group RSS at 50ms, AS64GiB and MALLOC_ARENA_MAX=2. Sampling is not a transient-peak guarantee. Cache oleans are trusted, user-writable external input; no source-to-olean attestation or full upstream rebuild. leanchecker shares the Lean installation. The unpruned diagnostic is corroboration, never a trusted numerical premise.

## Contents and provenance

proof/{Defs,BoolProbe,Checker,Endpoint}.lean are literal author bytes. ReviewAudit and ReviewSanity are clearly separate reviewer supplements; no frozen mathematical source is edited. PROOF.md is the ordinary author proof. sources/364095.jsonl is the exact raw MathDB line; sources/palette.pdf is the actual five-page primary v1 PDF and its acquisition receipt is adjacent. source-manifest.json hashes every source package member except itself; archive-hashes.json binds the ZIPs. The previous author ZIP hash is 2a47240b21c89a5cbc65e6a323a9a59dc3097c3479e15301b7fbdd01f1cd46cd; that old ZIP omitted the ordinary proof and raw line now included.

The full dossier contains copied independent reviews, receipts, full historical type inventory, primary comparison bodies, draft manuscript and new replay logs. Historical failed attempts are described honestly in evidence/author/ATTEMPTS.md and technical REVIEW.md. Unused Case files, failed oleans, huge dependency caches and expanded proof dumps are omitted. Copied historical scripts record their original environments; use the top-level portable replay.py for this package.

## Paper generation

The canonical PDF was generated with write_paper.py using ReportLab; paper-content.json stores the complete seven-page content and references. paper.tex is a self-contained LaTeX transcription, not the PDF build engine. No LaTeX installation was available in this task environment, so its compilation is not attested. To regenerate the PDF use Python with ReportLab installed: python3 write_paper.py. Render all pages using pdftoppm -r 100 -png paper.pdf qa/page, then inspect each. qa/receipt.json describes the actual visual QA. References are inline numbered entries; there are no unresolved citation macros. PDF metadata identifies the draft and AI assistance without fabricated human authorship. The PDF-skill operation marker was run once before authoring.

## Claims and limits

No arbitrary four-label coloring of K5 distinguishes all ten triangles by SETS. This negates Conjecture 5 of arXiv:2407.19050v1 at five. No exact tau_s(5), smallest counterexample, general corrected formula, infinite family, asymptotics, multiset refutation or worldwide priority is claimed. The qualified source review's selected-body, current-served-v1 and access limits remain in force; no fresh literature search was conducted here. Root final replay and manuscript review remain pending.
