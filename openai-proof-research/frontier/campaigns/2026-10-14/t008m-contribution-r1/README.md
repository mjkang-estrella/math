# T008M independent contribution gate, round 1

Verdict: **TECHNICAL** for the full unchanged frozen T008M scope. Not countable. This is not a proof verdict or a campaign acceptance. Read review.md and reading-and-limits.md together.

Files:

* review.md: verdict, operation decomposition, numbered required (R1–R4) and optional (O1–O4) objections, independence note.
* reading-and-limits.md: exact reading, search and proof limits.
* checkpoint.md: final state.
* author-identity-replay.json, author-integrity-controls.json: frozen author packet identity replay and copied mutation controls.
* primary-provenance.json: URLs, retrieval method and SHA256 of third-party bodies. Bodies are in private/primary/, which is git-ignored and not for redistribution.
* reviewer-sanity.py, reviewer-sanity-result.json: one finite illustration of the reviewer's unweighted remark.
* controls.py, integrity-controls.json: copied mutation controls for both packets.
* verify.py, manifest.json: identity verifier and exact inventory.

Verify with the manifest SHA256 supplied separately by the reviewer:

```
python3 verify.py --anchor EXTERNAL_MANIFEST_SHA256 --private --source-tree /absolute/path/to/sources/preprints-tree.json
```

`--author-dir` defaults to the sibling frozen packet `../fresh-arithmetic-discovery-r28`; pass it explicitly when verifying a copy elsewhere. The verifier is read-only, offline and uses only the Python standard library. It rejects symlinks at the script, root or any ancestor, symlinked, hardlinked or nonregular entries, and any file or directory not listed. It checks every payload hash, the frozen author packet's four external anchors, the canonical source tree hash and the 14 source008 Git blobs, and, with `--private`, the exact private inventory and primary-body receipts. Without `--private` the private subtree is still scanned for links and nonregular nodes, but its membership is not checked. A wrong anchor exits nonzero. It makes no mathematical inference.

Original prose CC BY 4.0; original code MIT. Third-party rights unchanged. No staging, commit, upload, shared edit or count change.
