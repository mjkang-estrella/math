# Reproduction

This is a draft dossier for MathDB 350979. Acceptance credit is zero. Run from an extracted source-only archive. Python 3, Linux /proc, the pinned Lean binaries and the pinned mathlib package cache are required. No network is used during replay.

```bash
python3 -I scripts/extract_safe.py circulant-source-only.zip fresh-copy
cd fresh-copy
export LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
export LEAN_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
python3 -I replay.py
```

The source archive contains its own safe extractor as well; use the dossier's script for the initial extraction. Choose a new extraction directory on every attempt. The driver refuses any existing local olean, validates SOURCE-MANIFEST.json, and checks the exact Lean version and commit. The mathlib revision is d13f23b723b8a846827a245b89c10fc7d3f11612; provide that cache through LEAN_PACKAGES. This is a dependency pin, not an independent rebuild or semantic validation of all upstream modules.

Every heavy child runs sequentially with at most two CPU cores, RLIMIT_CPU 120 seconds, a 140-second wall watchdog, sampled aggregate process-group RSS at most 6 GiB, and MALLOC_ARENA_MAX=2. Child output goes to logs/ and receipts to receipts/. RSS monitoring samples shared pages conservatively and is not a transient-peak guarantee. No child is intentionally left running.

The driver independently checks all 128 classification cases and all positive coverage witnesses, builds Circulant, Bridge, Endpoint, Audit, AuditFull and the two positive controls, and checks each module in a separate leanchecker process. Never combine checker module arguments: the review's combined attempt exceeded its RSS cap. All Lean builds use -j1 -DwarningAsError=true. AuditFull prints all 52 local declaration types, opaque bodies, flags and transitive axioms. Only propext, Classical.choice and Quot.sound are allowed. The positive order-16 control contains 560 paths. The mutation negation is a positive control. Both files in negative/ must fail with a false-decision diagnostic; nonzero status caused by a resource limit or missing import is not a pass. A repeated replay must refuse stale oleans.

The original four modules have byte identity recorded in MODULE-HASHES.json. The original supplied ZIP and its mandated SHA-256 are retained in evidence/. The exact MathDB raw line and its SHA-256 are in sources/. Original source bodies, access receipts and review evidence are retained in the full dossier; SOURCE-MANIFEST.json covers source-replay inputs. The full manifest excludes itself and ZIPs to avoid self-reference; archive-hashes.json binds ZIPs separately. Before/after bindings cover all 372 original frozen input files.

The source-only ZIP omits generated local oleans, replay outputs and bulky source bodies. It includes proof sources, negative controls, portable drivers, certificates, paper source, ordinary proof and pins. The full ZIP also includes the draft PDF, rendered page images, source copies and verification receipts; no local oleans are shipped. Build the paper with Python plus ReportLab using `python3 -B paper/build_paper.py`; the PDF was built with the existing Codex runtime's Python/ReportLab. Render every page using `pdftoppm -scale-to 1100 -png paper/circulant-draft.pdf qa/page`. See receipts/pdf-qa.json for visual inspection. The journal body was inaccessible (403); it was not read or retried. No worldwide priority is claimed.
