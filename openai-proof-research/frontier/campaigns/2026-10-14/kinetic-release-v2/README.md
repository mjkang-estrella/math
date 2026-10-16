# Kinetic corrected-edition publication-package machinery

Preparation snapshot, 2026-10-14. **Final corrected-edition review and parent integration are pending here.** No acceptance, campaign-count change, final publication archive, upload or submission is made by this task. The active `kinetic-manuscript-review-r2/` directory was not read.

The primary paper is [the consolidated 19-page PDF](../kinetic-manuscript-consolidation/output/pdf/main.pdf), with its frozen TeX, 57-output manifest and 107-record historical input manifest. The original manuscript and its first-round PASS remain historical evidence for different bytes. The old `kinetic-release/` is unchanged, including its pending gate and old manuscript bindings.

Author: **Myeongjin Kang**, no affiliation. Original prose/paper: **CC BY 4.0**. Original Python/Lean: **MIT**. Retain third-party rights and notices. See [SOURCE-AND-RIGHTS.md](SOURCE-AND-RIGHTS.md), [INVENTORY.md](INVENTORY.md), [STATUS.md](STATUS.md) and [GATE-INTEGRATION.md](GATE-INTEGRATION.md).

## Preparation checks

From the research root:

```sh
python3 -I frontier/campaigns/2026-10-14/kinetic-release-v2/assemble.py --check
python3 -I frontier/campaigns/2026-10-14/kinetic-release-v2/check_preparation.py
```

`assemble.py --check` verifies the explicit selection, every corrected output, historical review bindings, and five finite programs. It writes no archive. `check_preparation.py` tests clean extracted trees, path and membership rejection, manifest schemas, trust/gate failures, changed bytes and receipts, deterministic ZIP bytes and no-overwrite behavior. Its two clearly labeled **PREPARATION-ONLY** ZIPs and extracted trees exist only inside a temporary directory and are deleted. Default assembly and verification reject the actual pending gate. Actual results are in [preparation-checks.json](preparation-checks.json); this receipt reports no positive final-gate end-to-end test.

All finite programs run on disposable copies. The 14 repair and 8 editorial controls and adversarial counterchart use exact rational checks. Proof-round-2 and the original manuscript review mix exact arithmetic with seeded floating-point calculations, 3-D charts, numerical bounds and Monte Carlo. The latter has 12 named checks. Their output JSON bytes must match the retained receipts exactly. These checks are finite support, not proofs of the analytic theorem, Jacobian, history construction, or novelty.

## Parent integration after actual final review

[GATE-INTEGRATION.md](GATE-INTEGRATION.md) defines an exact, separate parent disposition, identity/provenance binding and trusted-hash contract. `bind_gate.py` can build a config from an **existing authenticated** parent disposition; it never makes a verdict or supplies an identity. No final review hashes or identities are anticipated in this snapshot.

After integration, the parent can run:

```sh
python3 -I frontier/campaigns/2026-10-14/kinetic-release-v2/assemble.py /new/path/package.zip \
  --gate frontier/campaigns/2026-10-14/kinetic-parent/ACTUAL-manuscript-config.json \
  --parent-disposition-sha256 ACTUAL_INDEPENDENTLY_TRUSTED_SHA256
```

This is a future parent operation, not authorization for this preparation task. The output parent must exist; existing files and symlink destinations are rejected. The assembler authenticates actual review members and parent disposition, reruns the finite programs, rechecks captured source bytes, then writes sorted fixed-time ZIP entries and verifies exact membership, CRCs and bytes. Only explicit inventory members and authenticated parent-selected review artifacts enter the package.

After extraction, from the extracted root:

```sh
python3 -I frontier/campaigns/2026-10-14/kinetic-release-v2/verify_bundle.py \
  --manifest-sha256 INDEPENDENTLY_OBTAINED_BUNDLE_MANIFEST_SHA256 \
  --parent-disposition-sha256 INDEPENDENTLY_TRUSTED_PARENT_SHA256
```

Both external hashes are optional for internal consistency checks. Without an independently obtained anchor, hashes do not establish who supplied the package. The verifier checks exact file and directory membership, rejects symlinks/nonregular files, reconstructs the selection and canonical metadata, and reruns finite programs without altering the extracted tree. `--preparation` only permits explicitly labeled pending test trees; it is not a release approval.

## Lean support reproduction

[rebuild_lean.py](rebuild_lean.py) and [lean-rebuild.json](lean-rebuild.json) are byte-identical copies of the authenticated old release files. [implementation-provenance.json](implementation-provenance.json) records exact source/destination hashes. **The receipt is historical, not a new compilation.** No expensive identical compilation was repeated. The support sources, checks, audit and dependency paths are unchanged; the shared freeze preflight now checks the corrected paper and is exercised by preparation checks.

For optional future reproduction in an extracted tree:

```sh
python3 -I frontier/campaigns/2026-10-14/kinetic-release-v2/rebuild_lean.py \
  --cache /path/to/existing/pinned/.lake/packages \
  --lean /path/to/lean-4.34.1-linux/bin/lean
```

The unchanged program requires Lean 4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and all nine lockfile dependency revisions. It compiles copied support source into a temporary olean and checks nine author and fourteen independent audit declarations. Only `propext`, `Classical.choice`, `Quot.sound` are allowed in its reports. Cached dependency oleans are reused; neither compiler nor dependencies are rebuilt. No network access or input-cache writes are performed. The actual historical run used `formal/.lake/packages` and the recorded local Lean binary. Fresh installation was not tested.

The retained formal review includes four rejected source mutations and their logs. Those mutation compilations were not repeated. Entering-root covariance, chronology Q, determinants/Jacobians, history existence, analytic estimates, tightness and the full path theorem are **not formalized**.

## Historical validation and typesetting

The corrected paper's `verify.py` requires all 107 input records, raw H sources and Poppler; it writes its own validation/finite receipts. The standalone release verifier deliberately requires only the selected inventory. [excluded-inputs.json](excluded-inputs.json) lists the precise omitted dependencies of three historical manifests. Restore them at their original paths in a disposable tree before running historical validators. Regenerating an upstream tree snapshot or a page render can produce different bytes.

The existing corrected validation records 213 structural checks and all 19-page QA; these are retained historical evidence and were not rerun here. No paper rebuild or fresh visual inspection was needed or performed. Rebuilding can alter PDF bytes and requires a new freeze, QA and review; it cannot replace this reviewed-input candidate silently. The retained frozen PDF is unchanged.
