# Reproduce the Cassinian dossier

Status: DRAFT; no priority claim, no accepted campaign credit. The literature gate has material unread bodies (see PRIOR-ART.md). Lean replay does not settle novelty.

## Inputs and pins

Use Linux, Python 3, Lean 4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52) and the cached mathlib dependency tree at revision d13f23b723b8a846827a245b89c10fc7d3f11612. pins.json binds the compiler and leanchecker binaries and lake-manifest.json. The cached upstream oleans are trusted, not rebuilt. Obtain these dependencies separately; they are not vendored. No network is used by replay.

Set LEAN_BIN to the directory containing lean and leanchecker. Set LEAN_PACKAGES to the directory whose immediate children are pinned lake packages with .lake/build/lib/lean subdirectories. On the task host:

```bash
export LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
export LEAN_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
python3 scripts/replay.py my-fresh-replay
```

Run from the dossier root. my-fresh-replay must not exist and must be a single child-directory name. The driver rejects source oleans in the root or formal/, validates the binary/manifest pins, creates that new directory, safely extracts 331705-proof-source.zip, rejects traversal, symlinks, duplicate entries and prebuilt oleans, and checks every extracted hash against MANIFEST.json. It then strictly compiles the three modules, runs leanchecker per module, runs the complete declaration audit and tests the two expected-failure controls. It never deletes user files or reuses local proof oleans. No cleanup is required for correctness; it retains its own fresh extraction and logs for review.

The source-only ZIP is also self-contained apart from upstream tools. Safely unpack it into an empty directory, then set SOURCE_ZIP to the absolute path of the original ZIP and invoke its scripts/replay.py with another new child-directory name. The source-only archive includes all Lean files, driver, this document, pins, ordinary proof, raw MathDB line, paper source and PDF builder. The full dossier ZIP includes that source ZIP, the draft PDF, source receipts, frozen review/adjudication copies, audit/build logs and manifests. Neither ZIP includes compiler dependencies or local oleans.

## What PASS means

Cassinian, Wedge and Sanity compile with -j1 -DwarningAsError=true and each passes leanchecker. Audit.lean enumerates local module origins including generated declarations; it prints full types and checks bodies, safety, partial flags and transitive axiom lists. Only propext, Classical.choice and Quot.sound are permitted. The tested run audited 62 declarations. Both Wedge.ordinary_refutation and Wedge.strict_refutation are literal negations of their displayed universal claims. Strict here refers to the domain's finite-boundary-point property; the ball conclusion being contradicted is ordinary starlikeness.

NegativeMidpoint must fail with a type mismatch when trying to use membership of y as membership of z. NegativeStrictSlit must fail with a type mismatch when trying to use wedge strictness for the slit. These controls assert only rejection of those substitutions, not general logical soundness. Supplementary exact optimizations in the paper are not Lean endpoint claims.

Each build/check invocation has two-CPU affinity, CPU 120 s, wall 140 s, AS 64 GiB and MALLOC_ARENA_MAX=2; a sampled 6 GiB descendant private-RSS guard is active. If a user systemd bus and systemd-run are available, MemoryMax=6G is applied; otherwise the receipt records null for the cgroup limit and the sampled guard remains. The supplied successful task-host receipts used the systemd scope. Python orchestration is low-memory; compiler subprocesses have the stated hard caps.

Logs are written under logs/, with per-command dated JSON resource receipts. replay-receipt.json records the archive hash, new extraction directory and all results. Log names are stable, so copy a prior receipt/log set if retaining multiple runs. A failure stops replay; inspect its log. All child processes finish before successful return.

## PDF and integrity

paper/manuscript.txt is the editable source. To rebuild the PDF install reportlab (tested 5.1.0) in an isolated environment; paper/build.py uses system Open Sans regular and bold fonts. It also accepts dependencies installed under tmp/pdfdeps. Run python3 paper/build.py, then pdftoppm -png paper/draft.pdf rendered/page and inspect every page. The delivered PDF has six pages; all six final PNGs were visually inspected. No charts or web browser are required.

before.json and after.json hash every regular file in the four read-only inputs. bindings-receipt.json verifies equality and byte identity of both Lean modules. source-manifest.json binds the Lean sources; the archive's own MANIFEST.json binds all source-packet members. dossier-manifest.json binds the full dossier payload; ARCHIVES-SHA256.json binds both ZIPs. Manifests do not attempt to hash themselves recursively.
