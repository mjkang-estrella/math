# Kinetic publication package machinery

Preparation snapshot, 2026-10-14: **independent manuscript gate pending**.
No publication archive has been created by this preparation task. Read
`STATUS.md` and `GATE-INTEGRATION.md` before assembling.

The paper is `../kinetic-manuscript/output/pdf/main.pdf` (19 pages).
Its exact TeX, PDF and 46-output manifest are frozen. This directory adds an
explicit file allowlist, an assembler, a clean-extraction verifier, a portable
cached Lean support rebuild and their preparation checks. It changes none of
the historical manuscripts, review verdicts or validation status strings.

Author: **Myeongjin Kang**, no affiliation. Original prose: **CC BY 4.0**.
Original code: **MIT**. The paper's two license files and the Lean license are
included. All third-party rights and notices remain in force. See
`SOURCE-AND-RIGHTS.md` for retrieval and excluded dependencies.

## Preparation checks from the research checkout

```sh
python3 -I frontier/campaigns/2026-10-14/kinetic-release/assemble.py --check
python3 -I frontier/campaigns/2026-10-14/kinetic-release/check_preparation.py
```

`--check` authenticates every explicitly selected byte and runs four copied
finite-control programs. It permits the pending template solely to inspect
preparation, writes no archive, and reports the pending state. The second
command additionally creates a disposable extracted-layout tree, checks exact
membership, and tests rejection of changed bytes, unsafe paths, symlinks,
unlisted files/directories and pending publication assembly. The temporary
tree is deleted. Both commands use Python's standard library and require no
upstream source download. Checks with fixed seeds also use floating-point
calculations; do not describe all four programs as exact rational proofs.

There are 14 named rational repair controls and 8 named rational editorial
controls, plus the rational adversarial counterchart program. The independent
proof-round-2 program exercises 4,000 finite histories, two physical examples,
exact-rational volume bounds, and numerical flux/energy bounds. All four
generated JSON receipts must match the frozen bytes. These checks do not prove
the analytic theorem or establish novelty.

## Final integration and assembly (parent only, after the actual gate)

`GATE-INTEGRATION.md` defines the required parent-authenticated JSON contract.
The parent supplies the actual config and independently trusted disposition
hash. The preparer has supplied neither an acceptance nor a placeholder hash.

```sh
python3 -I frontier/campaigns/2026-10-14/kinetic-release/assemble.py /new/path/package.zip \
  --gate frontier/campaigns/2026-10-14/kinetic-parent/ACTUAL-CONFIG.json \
  --parent-disposition-sha256 ACTUAL_PARENT_SHA256
```

The output parent directory must exist. An existing destination is never
replaced. The assembler rejects a pending gate before writing an archive,
checks the exact reviewer/source/PDF bindings, reruns the finite controls,
rechecks captured inputs, writes deterministic ZIP entries, then verifies
membership, CRCs and captured bytes. Only explicit allowlist records and
parent-configured authenticated gate records are included. No raw external
paper, dependency cache, `.olean`, `.ilean` or other build artifact is selected.
The reviewed PDF and page QA PNGs are deliberate binary assets.

After extraction, run from the extracted root:

```sh
python3 -I frontier/campaigns/2026-10-14/kinetic-release/verify_bundle.py
```

This checks every included file's SHA256 and byte length, exact membership
(including rejection of extra directories), the frozen manuscript, the
parent/reviewer binding, and the four finite-control outputs in disposable
copies. `--manifest-sha256 TRUSTED_HASH` additionally pins the bundle manifest
to an independently obtained hash. Without an external hash, this provides
internal consistency, not a digital signature or proof of who supplied it.
Default verification rejects pending-gate bundles. `--preparation` exists
only for explicitly labeled disposable preparation tests.

The preparation snapshot's `gate.json`, README and STATUS remain historical
records if a later package includes them. In that case, the selected actual
config and `BUNDLE-MANIFEST.json` record the later integration separately;
do not rewrite frozen historical status strings.

## Lean support reproduction

```sh
python3 -I frontier/campaigns/2026-10-14/kinetic-release/rebuild_lean.py \
  --cache /path/to/existing/pinned/.lake/packages \
  --lean /path/to/lean-4.34.1-linux/bin/lean
```

The tested cache is `../formal/.lake/packages` in the research checkout; it is
not included. The tested binary is under
`/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin`.
The script checks Lean 4.34.1's compiler commit and mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`, compiles copied source to a new
temporary olean, checks nine author declarations and fourteen independent
audit declarations, and permits only `propext`, `Classical.choice` and
`Quot.sound`. All nine dependency Git revisions must match the Lake lockfile;
their precompiled oleans are reused, not independently rebuilt or certified.
It neither writes to nor rebuilds the dependency cache. It does
not invoke Lake or download dependencies. A clean network installation and a
rebuild of Lean/mathlib themselves were not tested. `lean-rebuild.json`
records the actual local disposable-copy run. The original Lake manifest and
toolchain are also retained for users provisioning their own dependencies.

Exactly nine algebraic supporting declarations are covered: pair momentum and
unit-normal energy, four affine identities, finite all-line energy under pair
replacement and its elastic specialization, and rational exponent arithmetic.
Entering-root selection/covariance, chronology Q, determinant/Jacobian,
history existence, analytic estimates, tightness and the path theorem are
**not formalized**. See the included independent `coverage.md` and review.

## Historical manuscript verification and typesetting

The historical `kinetic-manuscript/verify.py` is not the standalone bundle
verifier. It requires all 54 inputs in `inputs.json`, including the eleven
excluded dependencies itemized in `excluded-inputs.json` (ten raw H files and
the original upstream tree index), their original paths, `pdfinfo` and
`pdftotext`. It also writes historical validation/check receipts; use only a
disposable copy. The parent already authenticated the 54 inputs, 46 outputs,
160 structural checks and all 19 page inspections. This release task does
not claim to have repeated that full historical audit.

The paper builds without the raw H source cache. For typesetting, use a
disposable manuscript copy with Python, Tectonic and Poppler, then run its
`build.py --tectonic /path/to/tectonic`. A new TeX installation may require
network downloads. Rebuilding can change PDF metadata/bytes and requires new
visual inspection; it does not replace the reviewed frozen PDF or its gate.
