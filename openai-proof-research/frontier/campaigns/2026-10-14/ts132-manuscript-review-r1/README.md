# TS132 independent full manuscript gate

Verdict: PASS_MANUSCRIPT against the unchanged full every-C and fixed-alpha theorem. See review.md and read-limits.md. The scoped formal implementation does not formalize the full theorem. This gate changes no campaign count and is not publication or external peer review.

Authenticate this review using an externally supplied manifest hash:

```sh
python -B verify_review.py --anchor EXTERNAL_MANIFEST_SHA256
```

The command checks exact membership, byte identities and evidence consistency read-only. Add `--dependency-parent /absolute/path/to/campaign` to recheck all five original anchored packages. Their private source bodies are not redistributed. Without that flag their identities are historical authenticated receipts, not live dependency checks.

For a fresh PDF rebuild, copy this review into a new working directory and run:

```sh
python -B work/support/build.py --tectonic /absolute/path/to/tectonic
```

Use Tectonic 0.17.0 with the prepopulated cache (the helper uses --only-cached) and Poppler. The helper sets SOURCE_DATE_EPOCH=1792108800, builds in a fresh temporary location, records compiler/log/byte identities and renders every page at 110 dpi. The expected PDF SHA256 is 580d2b10d7d74860a12c4f8ce4e066205b03b70b8b53e3a24b79ea8938efbdb5. Retained review rebuild bytes are identical to the final manuscript; all nine fresh renders were independently viewed. visual-qa.json supplies per-page observations and raster hashes. A new execution alone is not a new visual inspection.

The copied build helper's receipt points to its conventional checks/visual-review.json path; independent visual evidence for this review is instead the top-level visual-qa.json. No author receipt is edited to impersonate independent inspection. Two underfull bibliography boxes are readable and nonblocking. No original manuscript or frozen package was modified.

In a disposable working copy, `python -B check_integrity_controls.py --output replay-controls.json` exercises positive, wrong-anchor, changed, missing, extra-file, extra-empty-directory and symlink cases. Adding replay evidence changes that copy’s sealed membership; preserve the original package read-only. The verifier and this control helper are identical original review code in the two gate packages.
