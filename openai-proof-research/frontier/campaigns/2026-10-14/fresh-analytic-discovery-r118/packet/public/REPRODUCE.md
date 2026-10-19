# Integrity reproduction

Use Python3 and the existing COMPLETE sources/preprints-tree.json. Read the detached hashes from the independently supplied handoff, not from an edited packet. From the repository, with ROOT set to this round's absolute directory:

```sh
python "$ROOT/packet/public/verify.py" --root "$ROOT" --tree sources/preprints-tree.json --finalhash DETACHED_FINAL_SHA256 --reporthash DETACHED_REPORT_SHA256
```

Both hash arguments are required. The verifier is read-only: it does not repair, reseal, fetch, or write. MANIFEST.json and FINAL.json are outside packet; the manifest enumerates exact packet files and directories, and FINAL binds the manifest, report, pin and complete-tree identity. Public source/primary registers are themselves manifest-bound. Symlinks, hardlinks, missing/extra files and directories are rejected.

To repeat integrity controls on temporary copies inside ROOT/controls:

```sh
python "$ROOT/packet/public/run-copied-controls.py" --root "$ROOT" --tree sources/preprints-tree.json --finalhash DETACHED_FINAL_SHA256 --reporthash DETACHED_REPORT_SHA256
```

The controls include a coherent altered report/manifest/final reseal checked against the OLD detached hash. They record results outside packet and compare the original packet and anchors before/after. These are byte-integrity tests, never mathematical, eligibility or contribution gates. No finite mathematical experiment was used in this round.
