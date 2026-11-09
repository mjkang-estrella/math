# Reproducing the MathDB 368807 dossier

This is a DRAFT dossier with zero accepted credit; root alone accepts. It refutes Conjecture 1 of arXiv:2506.10671 with a vertex of P^8_ASEP that is adjacent to no tour.

## Contents (source-only archive)

| Path | What |
|---|---|
| `PROOF.md` | the ordinary proof |
| `paper/manuscript.md`, `paper/build_paper.py` | the draft paper source and its PDF builder |
| `mathdb/368807.jsonl` | the exact MathDB raw line, SHA-256 `c215c90f1c340a3c289ccffc287ce0af7f9eb7bca8273ba6e1a9140a682f1067` |
| `lean/*.lean` | 21 proof modules plus the unused helper `PermOrder.lean`, byte-identical to the frozen `expanded-corpus-r96/lean` (hashes in `pins.json`) |
| `lean/README-frozen.md` | the frozen packet README, copied byte-identically; its replay paths refer to the original lane |
| `audit/AuditLib.lean`, `audit/Audit.lean` | the full declaration audit |
| `negative/*.lean` | 1 positive and 6 negative controls |
| `tools/replay.py` | portable strict replay driver |
| `tools/watchdog.py` | per-call resource caps |
| `tools/safe_extract.py` | safe ZIP extraction |
| `tools/check_arith.py` | exact stdlib cross-check: vertex facts, 5040 certificates, n = 4 control |
| `pins.json`, `upstream-lake-manifest.json` | toolchain and dependency pins |
| `MANIFEST.json` | SHA-256 of every file in the archive |

## Pins

- Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`. The `lean` and `leanchecker` SHA-256 values are in `pins.json`.
- mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and its dependencies as listed in `upstream-lake-manifest.json`, used as prebuilt oleans.
- Reference locations on the original machine:
  - `LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin`
  - `LEAN_PACKAGES=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`

## Steps

```sh
python3 -I tools/safe_extract.py asep-368807-source.zip NEW_DIR extraction-receipt.json
cd NEW_DIR
LEAN_BIN=... LEAN_PACKAGES=... python3 -I tools/replay.py ../replay-out
python3 -I tools/check_arith.py lean ../arith.json      # optional exact cross-check
python3 -I paper/build_paper.py ../draft.pdf [REPORTLAB_DIR]   # optional; needs reportlab 5.1.0
```

`replay.py` refuses an existing output directory and any `.olean`, `.ilean` or `.lake` inside the dossier. It then runs these steps:

1. Verifies `MANIFEST.json` and the pins.
2. Checks byte identity of the 22 Lean modules.
3. Scans the 21 proof modules, with comments and strings stripped, for `sorry`, `admit`, `axiom`, `unsafe`, `partial`, `opaque`, `native_decide`, `ofReduceBool`, `ofReduceNat`, `implemented_by`, `extern`, `#eval`, `run_cmd`, `elab`, `macro` and `debug.skipKernelTC`.
4. Builds the modules in dependency order, one at a time, with `lean -j1 -DwarningAsError=true` into a fresh `build/`:
   - `ASEPData`, `ASEPCheck`, `ASEPCover`;
   - `ASEPCerts0` to `ASEPCerts11`;
   - `ASEPDefs`, `ASEPSound`, `ASEPVertex`, `ASEPBridge`, `ASEPMain`, `ASEPArcs`;
   - then `PermOrder` and `AuditLib`.
5. Runs `leanchecker` on each of the 22 modules.
6. Compiles `Audit.lean`, which emits one JSON record per local declaration and fails if any check fails, and re-checks the records in Python.
7. Runs the controls.
8. Writes `replay-receipt.json`, with `all_ok`.

Every Lean call goes through `tools/watchdog.py`, one at a time, with these caps:

- 2 CPUs (affinity);
- `RLIMIT_CPU` 120 s;
- wall 140 s;
- sampled process-tree RSS of at most 6 GiB, sampled every 0.05 s, with the process group killed above the cap;
- `MALLOC_ARENA_MAX=2`;
- a `systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0` backstop when available.

The child environment contains only:

- `PATH=LEAN_BIN:/usr/bin:/bin`;
- `HOME`, set to a fresh directory inside the output;
- `LANG`;
- `LEAN_PATH`, holding the pinned package libraries and the fresh `build/`;
- `MALLOC_ARENA_MAX`;
- the systemd session variables.

`PermOrder.lean` is a frozen helper that no proof module imports. Its `#eval` writes `perm-order.txt` into the replay's `src/` directory, and the replay compares that file with the frozen copy.

## Trust limits

- The mathlib and dependency oleans are prebuilt and trusted; they are not rebuilt.
- `leanchecker` runs per module without `--fresh`, from the same installation as the compiler.
- RSS is sampled rather than continuously enforced, apart from the systemd memory limit.
- `check_arith.py` and the rank histogram cited in the paper are cross-checks, not part of the proof.
