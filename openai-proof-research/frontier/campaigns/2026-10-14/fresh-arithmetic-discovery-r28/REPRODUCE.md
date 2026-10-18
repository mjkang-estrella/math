# Private author packet T008M

Read scope-008.md, candidate-008.md, source-and-credit.md, formal-interfaces.md and reading-limits.md in that order. screen-200.md is a separate rejected pre-freeze screen. No file in this packet grants a review or acceptance gate.

Python3 standard library is sufficient. From a copied packet directory:

```
python diagnostic-008.py
python diagnostic.py
python verify.py --manifest-sha256 EXTERNAL_MANIFEST_SHA256 --verifier-sha256 EXTERNAL_VERIFIER_SHA256
python controls.py --manifest-sha256 EXTERNAL_MANIFEST_SHA256 --verifier-sha256 EXTERNAL_VERIFIER_SHA256
```

Obtain both exact anchors from the parent handoff, not a newly calculated value from an untrusted copy. Authenticate verify.py against the external verifier hash before executing it. The public-only verifier permits private/ to be omitted. Add `--private` to authenticate all43 private source/primary bodies. Add `--source-tree /absolute/path/to/sources/preprints-tree.json` to compare all39 non-PDF receipts and the42-blob family inventory against the authenticated complete canonical tree. PDFs are in the canonical inventory but were not downloaded. The three receipt files identify all43 private files.

controls.py requires the full private local packet and runs19 cases on disposable copies: positive; wrong manifest anchor; wrong verifier anchor; modified/deleted proof; extra public file; symlink; changed manifest; changed verifier; changed private body; extra private body; public-only positive; extra empty directory; root/ancestor links; hardlink; FIFO; nested manifest; and self-reseal. It leaves the original packet unchanged. Capture output outside the packet to preserve strict inventory. No package installation, network, Lean, PDF renderer or external service is required for replay.

These integrity controls authenticate fixed bytes. The two finite diagnostics test specific calculations. Neither substitutes for the human all-scope proof or independent contribution judgment.

The first inventory seal was superseded after failed validation; provenance/seal-repair.md and the preserved original bytes record the repair. Only the replacement external anchors are operative.
