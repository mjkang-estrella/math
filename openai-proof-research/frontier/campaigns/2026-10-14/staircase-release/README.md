# Staircase publication preparation

Myeongjin Kang, no affiliation. Local draft, 2026-10-15. Final independent manuscript gate pending. This directory prepares publication machinery; it awards no acceptance, assigns no R number, changes no count (user-reported 3/10), and performs no upload or submission.

The frozen six-page paper proves, for every integer m ≥ 1, an integral regular summand in the staircase Specht tensor cube, generated in the specified order by v_R ⊗ v_R ⊗ v_C, with an explicit integral G-linear retraction. The split identity survives extension to every commutative unital ring, including nonflat extensions and the zero ring. `FORMAL-COVERAGE.md` integrates the actual independent scoped Lean PASS. The full staircase theorem is not formalized. The paper's bytes and its honest no-full-Lean statement are preserved.

`allowlist.json` fixes the 130 foreign payload files and their digests. They are frozen under `payload/` at their eventual project-relative paths. `output-manifest.json` fixes this preparation's top-level files (excluding itself). The final ZIP contains those two explicit selections plus actual authenticated final-gate evidence, with one `BUNDLE-MANIFEST.json`; it never recursively includes the workspace. `INVENTORY.md` and `RIGHTS.md` explain the selection and historical-manifest limits.

Run preparation checks from any working directory (replace the prefix below with the actual absolute path if needed):

```sh
python3 -I frontier/campaigns/2026-10-14/staircase-release/check_preparation.py
python3 -I frontier/campaigns/2026-10-14/staircase-release/reproduce_finite.py
```

Both use disposable directories inside this preparation folder. The first checks pending-gate rejection, hashes, safe archive transport and negative cases. It creates only explicitly labeled PREPARATION_ONLY test archives and deletes them. No positive final-gate end-to-end verification is claimed. The second reruns the two historical finite programs, compares their entire expected outputs and reproduces 3,072 basis-interface comparisons. These are finite corroboration, not an all-m proof or a fresh independent review.

For optional Lean reproduction, provide an existing exact compiler and existing compiled dependency cache. All nine Git revisions and the compiler commit are checked. `--check-setup` verifies prerequisites and disposable runner paths without recompilation:

```sh
python3 -I frontier/campaigns/2026-10-14/staircase-release/rebuild_lean.py \
  --lean /absolute/path/to/lean-4.34.1/bin/lean \
  --cache /absolute/path/to/existing/.lake/packages --check-setup
```

Remove `--check-setup` to run the original author rebuild and all eight independent review stages, including the three semantically rejected mutations, on disposable copies. Allow several minutes. Capture stdout outside frozen artifacts if retaining a new receipt. `REPRODUCTION.md` gives setup, trust boundaries, and the important distinction between the original author verifier, frozen review verifier and portable wrapper. Rebuilds write time-dependent receipts and must never run in the frozen originals.

The parent must first finish and authenticate the actual `staircase-manuscript-review-r1` review. `GATE-INTEGRATION.md`, `gate.schema.json` and `parent-disposition.schema.json` specify the separate parent disposition and actual manifest-member bindings. Do not edit `gate-pending.json` into an approval. After the parent has made its actual decision and independently communicated its disposition SHA256:

```sh
python3 -I frontier/campaigns/2026-10-14/staircase-release/bind_gate.py \
  --parent-disposition frontier/campaigns/2026-10-14/staircase-parent/ACTUAL-manuscript-disposition.json \
  --trusted-parent-sha256 ACTUAL_INDEPENDENTLY_TRUSTED_SHA256 \
  --output frontier/campaigns/2026-10-14/staircase-parent/ACTUAL-manuscript-gate.json
python3 -I frontier/campaigns/2026-10-14/staircase-release/assemble.py \
  --gate frontier/campaigns/2026-10-14/staircase-parent/ACTUAL-manuscript-gate.json \
  --trusted-parent-sha256 ACTUAL_INDEPENDENTLY_TRUSTED_SHA256 \
  --output /absolute/path/to/NEW-local-package.zip
python3 -I frontier/campaigns/2026-10-14/staircase-release/verify_bundle.py \
  /absolute/path/to/NEW-local-package.zip \
  --trusted-parent-sha256 ACTUAL_INDEPENDENTLY_TRUSTED_SHA256
```

These are future parent instructions, not commands already performed. Add repeatable `--artifact` project-relative actual review members to `bind_gate.py` if appropriate. `--root` overrides the repository/extracted-bundle root. Assembly uses frozen payload copies and reads only the explicit later parent/reviewer evidence from that root. Output creation is exclusive and deterministic; no existing ZIP is overwritten. Verification rejects symlinks, escaping/noncanonical names, duplicate ZIP/JSON/manifest entries, missing or altered bytes and inconsistent gate bindings, then uses a clean extraction and the actual frozen formal-review verifier. An independently received `--archive-sha256` can also be checked.

`metadata-zenodo.json` and `metadata-mathdb.json` are local drafts with unassigned identifiers/routing, not API submissions. The parent assigns any eventual release number and publication identifiers only after the required gates. No DOI, staircase publication URL or MathDB record has been invented.
