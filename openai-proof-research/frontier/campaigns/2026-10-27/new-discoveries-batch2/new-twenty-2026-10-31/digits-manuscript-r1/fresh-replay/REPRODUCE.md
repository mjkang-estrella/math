# MathDB 356756: portable certificate replay

This is a draft dossier, not acceptance. No network access is required for Lean replay.
All scripts write only within their extraction/lane. Use a new directory for each replay.

Pinned inputs:

- Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52.
- mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and its pinned package closure.
- Local Lean binary directory: `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin`.
- Local package cache: `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`.
- `formal/Digits.lean` and `formal/Audit.lean` are exact frozen copies. `formal/AuditFull.lean` is new in this packet, adapted from the independent review's strengthened instrumentation.

Extract `digits-source-only.zip` safely into an EMPTY directory (reject absolute paths, `..`, symlinks and duplicate names). Then run:

```sh
export LEAN_BIN=/path/to/lean-4.34.1-linux/bin
export LEAN_PACKAGES=/path/to/pinned/formal/.lake/packages
python3 -I replay.py
```

`LEAN_BIN` must be a directory containing both lean and leanchecker. `LEAN_PACKAGES` must contain the pinned package directories with `.lake/build/lib/lean` caches. Cached upstream oleans are trusted, not regenerated or source-attested here. `evidence/lake-manifest.json` records the package revisions. The driver checks the full Lean version/commit, clears inherited Lean import/plugin paths, verifies SOURCE-MANIFEST.json before compilation, and refuses any existing `.olean*` in the extraction. It uses only the extraction and configured package caches as its import path.

Modules build sequentially using `lean -j1 -DwarningAsError=true`; leanchecker runs separately for each. Each subprocess has affinity to at most two CPUs, a 120-second RLIMIT_CPU, a sampled process-group RSS watchdog at 6 GiB, a 140-second wall watchdog and MALLOC_ARENA_MAX=2. Poll interval is 0.1 seconds, so the RSS cap is sampled rather than a hard allocation limit. The driver joins each subprocess and records exit, time and peak sampled RSS. It never runs heavy jobs concurrently.

The FULL AuditFull output contains all 45 local declarations, including generated ones: 45 full types, 45 bodies using value? (allowOpaque := true), unsafe/partial flags and transitive axiom lists. It fails on unsafe/partial declarations, local axioms, missing ordinary bodies or any axiom outside propext, Classical.choice, Quot.sound. The metaprogram is audit instrumentation, not an axiom in the theorem. Source token screening applies to the frozen proof; audit instrumentation necessarily mentions axiom and safety APIs.

The negative controls are false propositions with deliberately unsuccessful proof attempts, not proofs using holes. `ExtraDigit.lean` tests inadmissibility of the enlarged p=13 digit set on all four explicit dimension-9 vectors. `QuadraticOnly.lean` attempts the false nonnegative gap at (5,0,8,3). Both must return ordinary Lean error code 1, without a watchdog kill. A second replay in the same extraction must refuse the generated oleans.

Successful receipts are under `fresh-replay/receipts/`, especially `replay.json`; complete audit bodies are in `fresh-replay/logs/build-AuditFull.log`. `receipts/extraction.json` binds the fresh extraction to the source archive. The full dossier includes replay artifacts for inspection; it is not itself a fresh build directory. Always extract the nested source-only archive for replay.

The manuscript source is `paper/build_paper.py`. It requires Python 3, ReportLab, and Liberation Serif/Mono and Symbola fonts; the local drafting dependency install is documented in `receipts/pdf-dependencies.log`. It creates `paper/digits-parity-draft.pdf`. The six rendered page images and visual inspection receipt are in qa/ and receipts/. A standalone same-cap runner is available as `python3 -I scripts/limited.py LABEL COMMAND ARG...`.

Frozen input bindings are in input-hashes-before.json and input-hashes-after.json. The input-copy manifest ties dossier copies to originals. DOSSIER-MANIFEST.json covers every delivered dossier file except itself and the full archive (to avoid self-reference). archive-hashes.json binds both ZIPs externally. Full prior-art search and HTTP receipts are copied from the review and root: they describe bounded earlier reads, not a new live clearance by this drafting pass. Root alone decides acceptance and performs its final independent replay and refresh.
