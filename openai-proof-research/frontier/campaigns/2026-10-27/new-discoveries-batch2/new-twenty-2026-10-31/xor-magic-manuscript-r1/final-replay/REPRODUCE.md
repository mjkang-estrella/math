# Reproduce the XOR-magic draft dossier

DRAFT; accepted credit 0, root acceptance pending. Campaign remains 14/20 beyond 39.

The source-only ZIP is self-contained apart from the pinned upstream tools and packages. No network is needed for Lean replay. Extract into a new empty directory using safe_extract.py (or an equivalent path-safe extractor). The driver refuses any existing local .olean or .olean.* file. It never deletes user files; its logs/tmp/home directories are local to that extraction. Actual HOME is retained; inherited Lean options and plugin paths are discarded.

```
python3 -B safe_extract.py xor-magic-manuscript-source.zip my-fresh-replay
cd my-fresh-replay
export LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
export LEAN_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
python3 -B -I replay.py
```

LEAN_BIN may be a binary directory or the full path to lean. LEAN_PACKAGES contains mathlib and the other package directories with cached .lake/build/lib/lean trees. Lean must be version 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52; mathlib must be d13f23b723b8a846827a245b89c10fc7d3f11612. The adjacent project lake-manifest.json is checked for the mathlib revision; alternatively set LEAN_LAKE_MANIFEST to that manifest before starting. Binary SHA-256 pins and the original dependency manifest are in pins.json and upstream-lake-manifest.json. The cached upstream oleans are trusted and not rebuilt. leanchecker is from the same installation, not an independent kernel implementation.

All 107 local Lean modules must build with -j1 -DwarningAsError=true and pass leanchecker. The full declaration audit checks local bodies, types, safety, partial flags, and transitive axioms; only propext, Classical.choice and Quot.sound are allowed. The DAG consistency checker validates full expression graphs and duplicate declaration identities. The source modules must be byte-identical to r5. The per-call wrapper restricts affinity to 2 CPUs, CPU to 120 seconds, wall to 140 seconds, samples aggregate descendant RSS against 6 GiB, and sets MALLOC_ARENA_MAX=2. Receipts report measured peak sampled RSS; transient peaks between samples are not continuously enforced. The minimal environment retains actual HOME, uses a pinned PATH, and packet-local TMPDIR. No upstream cache writes are requested.

Seventeen negative controls must fail after imports resolve. They test false concrete label, sum, degree, field, seed, orientation, cycle, incidence, affine, scalar and endpoint claims. BadFinalEndpoint attempts to specialize the corrected range to forbidden closed degree 12 at exponent 4; BadPrintedFromCorrected attempts the invalid printed inference. These controls assert only the indicated rejection, not universal detection of malicious edits. Logs are under logs/ and logs/replay-receipt.json is created only on total success.

PROOF.md is the corrected ordinary proof (the paper text); the historical focused PROOF.md is preserved under evidence and has outdated formal-status statements. base-data.json includes adjacency masks plus direct parents/ranks for all 32 finite witnesses. Run certify_bases.py from the dossier root to verify them independently using standard Python (it reads formal/ and writes only receipts/ and base-data.json).

paper-source.md is the expanded readable manuscript; manuscript.md is its template and build_paper.py fills it using base-data.json and Literal.lean. Run python3 -B build_paper.py with ReportLab available (tested 5.1.0), using local-deps/ if supplied or an installed ReportLab. System fonts are Liberation Serif/Mono, Noto Sans Math and Symbola; see build_paper.py. Then render every page with pdftoppm -r 110 -png xor-magic-draft.pdf qa/page and inspect all nine images. The full dossier preserves the final renderings and QA receipt. PDF author metadata explicitly identifies the AI-assisted draft.

source-manifest.json hashes every source ZIP member except itself. dossier-manifest.json hashes each full-dossier payload member except itself. archive-hashes.json is external and hashes both ZIPs. Neither manifest recursively hashes itself or its containing archive. The full ZIP includes the exact verified source ZIP, paper PDF, corrected proof, source copies, replay logs, audits, QA and frozen-binding receipts; it omits generated oleans and expression-DAG bulk (their check and audit logs remain). Root alone performs final acceptance review. Batal's construction-paper body is unread; no new live prior-art check or priority claim is made.
