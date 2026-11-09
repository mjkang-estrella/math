# Reproducing the Lean refutation of MathDB 359279

This manuscript lane did NOT run Lean, lake or leanchecker; root performs the final fresh replay.

## Pins

* Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
  * Binary directory used by root: `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin`.
* mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
  * Prebuilt package cache: `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`.
  * The manifest is `evidence/lake-manifest.json`, sha256 `d00ceb5cba2155c7c9bcc5aba05a755733331b75ded4a7f0f009320e3cde5bb8`.
* The cached upstream oleans are trusted. They are not rebuilt from source.

## Steps

```bash
mkdir fresh && cd fresh
unzip -q ../tabminors-source-only.zip
LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin \
LEAN_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages \
python3 -I replay.py
```

## What `replay.py` does

1. Refuses to start if any `.olean`, `.ilean` or `.c` file already exists.
2. Checks every hash in `SOURCE-MANIFEST.json`, scans for forbidden tokens, and checks the Lean version, Lean commit and mathlib git HEAD pins.
3. Builds `TabMinors`, `AuditFull` and `Controls` in sequence with `lean -j1 -DwarningAsError=true -o M.olean M.lean`, with `formal/` as the working directory.
4. Runs `leanchecker` on each of the three modules.
5. Checks that the `#print axioms` line for `not_conjecture` lists exactly `[propext, Classical.choice, Quot.sound]`.
6. Checks the AuditFull output. It must report exactly 140 declarations, none unsafe or partial, all with bodies, and no axiom outside the three above.
7. Runs `negative/NegControl1.lean` and `negative/NegControl2.lean`. Each must fail, and with the expected error.
8. Runs a freshness self-test: a second invocation must refuse to start.
9. Writes `receipts/replay.json` (status PASS or FAIL, per-step receipts, olean hashes) and keeps logs in `logs/`.

## Resource caps

Every process runs under these caps:
* 2 CPUs;
* `RLIMIT_CPU` of 120 s;
* 140 s of wall time;
* a 6 GiB RSS limit on the process group, enforced by a sampled watchdog;
* `MALLOC_ARENA_MAX=2` and `LEAN_NUM_THREADS=1`.

Only one heavy process runs at a time. In root's earlier replay of the same bytes, the largest step peaked at about 2.6 GB and 22 s.

## Expected result

```
PASS: strict replay of TabMinors/AuditFull/Controls, leanchecker x3, 140-declaration audit, 2 negative controls rejected
```

Root's previous PASS of these exact bytes is in `evidence/root-parent-check/` of the full dossier.

## Optional non-Lean checks

These need Python 3 and take well under a second:
* `python3 -I -B scripts/check_pair.py formal/TabMinors.lean` checks the main pair, the Lemma 3 formula, and agreement with the Lean literals A8 and B8.
* `python3 -I -B scripts/check_pair.py --c5` checks the n = 16, k = 11 hook pair.
