# Reproduce MathDB 380362 — DRAFT, zero accepted credit

No network, Lake update, dependency build, or cache write is needed. Linux Python 3 is the replay runtime. All writes must stay inside a fresh extraction. No acceptance is implied; root alone accepts. Count remains 9/20 beyond 39.

Pins: Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Binary SHA-256 values and literal Loop.lean hash are in pins.json. The LEAN_PACKAGES tree must contain matching prebuilt dependency libraries under each package's .lake/build/lib/lean. Cached dependencies are trusted; the driver does not source-attest every upstream olean. The recorded dependency manifest is provenance, not a substitute for independently building dependencies.

Use scripts/safe_extract.py from this dossier to reject absolute paths, parent traversal, symlinks and duplicates, and require a nonexistent destination:

```
python3 -I scripts/safe_extract.py source-only.zip /path/to/new/extraction
cd /path/to/new/extraction
LEAN_BIN=/path/to/lean-4.34.1-linux/bin \
LEAN_PACKAGES=/path/to/formal/.lake/packages \
python3 -I -B scripts/replay.py
```

The local run used LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin and LEAN_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages.

The driver checks the source manifest and binary pins, refuses any existing olean and existing replay receipts, strictly builds Loop, ReviewAudit and AllAudit with -j1 -DwarningAsError=true, and runs leanchecker on each. ReviewAudit is a frozen reviewer supplement; AllAudit inventories all declarations of both substantive modules, including generated declarations, checking unsafe status, local axioms and transitive axioms. Only propext, Classical.choice and Quot.sound are allowed. Loop has exactly 28 declarations. The AllAudit module is itself kernel rechecked. Inspect build-AllAudit.log for full declaration names, types and axiom sets.

Every child call has affinity to at most two CPUs, RLIMIT_CPU=120 s, wall watchdog=140 s, RLIMIT_AS=64 GiB, MALLOC_ARENA_MAX=2, and a sampled (100 ms) 6 GiB guard on process-group private memory from smaps_rollup Private_Clean+Private_Dirty+Private_Hugetlb. Total VmRSS is separately sampled and reported. A user systemd scope with MemoryMax=6G is probed and used if available; the receipt records availability or the probe failure. Sampling is not an instantaneous peak guarantee. The driver removes only the temporary files it created inside formal/; receipts persist. No shared cache deletion or mutation is performed.

Five negative controls require compilation failures with specific messages: distance=96 by decide; the constant map as the nonassociative loop's associator; using the refutation as a proof of SourceClaim; sorry under strict warning handling; and a theorem using an added forbidden axiom under the same axiom whitelist filter. These are tests of those particular false statements or enforcement paths, not a general completeness guarantee. Positive reviewer checks include arbitrary-bijection inequivalence and the correct basis associator. The independent reviewer integer diagnostic is evidence only; its preserved exact.json is not the replay's kernel certificate.

Paper source: paper-source.md, rendered by scripts/write_paper.py with ReportLab (tested 5.1.0), Liberation Serif/Mono and Noto Sans Math system fonts. Install ReportLab in your own environment if absent. No dependencies are installed by replay. Run `python3 -B scripts/write_paper.py`, then `pdftoppm -scale-to 1100 -png paper.pdf qa/page`. The frozen author ordinary proof is in evidence/author/; PROOF.md contains the complete new ordinary proof. The source archive includes paper/proof source but no compiled output. The full dossier additionally includes the PDF, rendered-page QA, frozen evidence and replay receipts. Manifests do not hash themselves; archive hashes live outside the corresponding ZIPs.
