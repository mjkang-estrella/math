# Portable strict replay (DRAFT; zero credit)

Prerequisites: Linux, Python 3, Lean 4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), and the pinned mathlib/package cache in pins.json. No network, Lake invocation or cache writes are performed. The supplied objects are trusted upstream dependencies, not bundled here. Binary and Mathlib.olean hashes must match pins.json. LEAN_PACKAGES denotes the directory containing mathlib and its sibling packages; LEAN_BIN contains lean and leanchecker.

From a directory in which you may create a new extraction:

```sh
python3 safe_extract.py source-only-proof.zip fresh
cd fresh
export LEAN_BIN=/path/to/lean-4.34.1-linux/bin
export LEAN_PACKAGES=/path/to/pinned/.lake/packages
python3 replay.py
```

Use a fresh extraction each time: replay refuses all existing oleans and existing replay receipts. It verifies source-manifest.json, builds in dependency order with `-j1 -DwarningAsError=true`, checks each module with leanchecker, inventories every generated/local declaration, and runs three expected elaboration failures. Receipts appear in replay-receipts; result.json must say PASS. The three failures test only the displayed mutations: ordered-factor confusion, using a non-induced path, and dropping triangle-freeness. They are not exhaustive mutation testing.

All subprocesses use at most two affinity CPUs, CPU 120 s, wall 140 s, AS 64 GiB, MALLOC_ARENA_MAX=2 and a sampled 6 GiB RssAnon+RssShmem guard. Total VmRSS is reported separately. A probed systemd user scope applies MemoryMax=6G when available. No driver deletes anything outside its fresh extraction; only its temporary rejected-mutation file is removed. Do not run against the original frozen packet. No upstream cache is modified.

The 12 frozen mathematical/control modules are 11 Sigma modules plus NegativeControls. The inspection drivers and reviewer supplements are separately labeled. The body audit permits only propext, Classical.choice and Quot.sound, and demands actual bodies, safe and nonpartial declarations. See declarations.json and original audit logs for full types and transitive axioms.

Manuscript regeneration uses write_paper.py (Python reportlab and DejaVu Serif fonts); paper-content.json contains the prose. Render with pdftoppm. The source-only ZIP omits PDF, rendered images, replay objects and receipts; the full dossier includes the final PDF, visual QA and completed replay receipts but excludes compiled objects/caches. Hash manifests are integrity bindings, not digital signatures or independent proofs. Frozen-before/after inventories bind every regular file in all six designated inputs; some initial orientation reads preceded the baseline, explicitly disclosed in SUMMARY.md.
