# Reproduce the draft dossier

This packet is a DRAFT, assigns zero accepted credit, and leaves root acceptance, registry refresh and independent paper review outstanding.

## Lean replay

Use a newly created empty directory INSIDE the assigned lane for verification. Check archive SHA-256 against archive-hashes.json. Inspect member paths and reject absolute paths, traversal and symbolic links before extracting edgepattern-source-only.zip. The source archive contains no compiled modules. Validate SOURCE-MANIFEST.json; do not transplant oleans.

```
export LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
export LEAN_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
python3 -I replay.py
```

LEAN_BIN is the executable (its parent is the requested binary directory), not the directory. Both variables can be changed for another installation of the same pins: Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Precompiled external package caches are trusted, not rebuilt. The replay records the actual Lean --version output. It sanitizes inherited LEAN/LAKE search settings and refuses preexisting oleans anywhere under its root.

The driver initializes a clean extraction, then executes one guarded subprocess at a time, stops at failure, and prints a final PASS line only after all stages succeed. For short tool calls use `python3 -I replay.py --init`, repeat `python3 -I replay.py --step` until DONE, then `python3 -I replay.py --finish`. Each step validates frozen source hashes and records completion plus compiled-module hashes; finish checks all compiled bytes and completeness. With no arguments it performs the same stages in one sequential loop. Do not use the no-argument mode if the outer execution environment limits job lifetimes. scripts/modules.json is a dependency order for 268 proof modules plus AuditR5. Every strict compilation uses -j1 -DwarningAsError=true; every leanchecker call contains exactly one module. AuditR5 performs the full generated-declaration expression inventory and axiom checks. The separate AuditToolSafety check inspects generated auditor declarations. Only propext, Classical.choice and Quot.sound are allowed. Canonical and inherited Audit/AuditR2/AuditR3/AuditR4 are preserved outside the build/proof closure. No proof source was edited.

The watchdog sets affinity to at most two CPUs, CPU limit 120 s, wall limit 140 s, MALLOC_ARENA_MAX=2, and samples private RSS every 0.05 s, killing at 5.75 GiB (below 6 GiB). Each guarded call is sequential. The full replay is 545 short guarded calls, never one uncapped Lean invocation. The existing-olean refusal is a separate lightweight Python call. Logs and resource receipts are in fresh-replay/logs/; the top-level receipts/replay-driver.log includes the final PASS line. An interrupted source extraction cannot be reused for a clean replay because it contains oleans.

Expected failures include the positive conjecture, wrong root, missing acyclicity, the false numeric lower bound on the concrete pattern (whose equality is proved in Concrete), and a false strict upper bound on the minimum tree value. Each must return an ordinary Lean error (exit 1), not timeout or resource kill. Existing-olean refusal is checked separately. Five false Lean controls plus this refusal must pass. AuditToolSafety must compile.

## Ordinary proof and paper

PROOF.md gives the complete ordinary proof, classification, closed evaluation rule and all 81 exact entries. paper/manuscript.md is the editable manuscript text; paper/build.py is the complete PDF typesetting source, with bundled fonts. To regenerate using Python with reportlab installed:

```
python3 paper/build.py
pdftoppm -r 110 -png paper/edgepattern-draft.pdf qa/page
```

Read all six rendered pages. qa/ and receipts/pdf-qa.json bind the delivered rendering. The proof uses no solver: receipts/closed-form-values.json has exact rational values; receipts/ordinary-math.json records equality with the input independent all-subset enumeration. The table scales values by 810000 to display integer entries. The 81 forms include one depth-1 tree; the other 80 have exact depth 2. The extension to depth-at-most is ordinary mathematics, not a Lean theorem.

## Provenance and archives

sources/342414.jsonl is the exact raw MathDB line, with its dedicated SHA-256 file. evidence/ preserves source v1/v6, thesis and citing-body copies, access receipts, previous review and root adjudication. INPUT-COPY-MANIFEST.json maps every copied frozen input to its origin/hash. input-hashes-before.json and input-hashes-after.json bind the inputs without modifying them. The two r5 archives and EDGE-PROOF.md must match TASK.txt's required hashes.

SOURCE-MANIFEST.json covers the source archive payload (excluding itself to avoid recursion). DOSSIER-MANIFEST.json covers the full dossier payload (excluding itself and the full ZIP). archive-hashes.json binds the ZIPs externally. The full dossier excludes redundant fresh-replay and interrupted-replay source copies and compiled binaries but retains every fresh replay log and resource receipt. A successful local replay is not campaign acceptance and makes no priority claim. Final SIAM body, the inaccessible heuristic body, an edge/vertex-colouring thesis body and MathDB comments remain unread.
