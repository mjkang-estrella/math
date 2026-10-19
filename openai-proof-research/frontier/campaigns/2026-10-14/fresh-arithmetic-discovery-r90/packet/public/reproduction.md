# Evidence verification

This is a prefreeze archive, with no mathematical test suite or frozen theorem. Research reasoning is in automorphism-feasibility.md and other-screens.md; actual reading limits govern every citation. Private preparation programs retain their original workspace assumptions and are not a portable research pipeline. They are not run by verification.

Use the detached FINAL and REPORT SHA256 values supplied in the handoff, not hashes invented from the packet being checked:

```sh
python -B "$R90/packet/public/verify.py" --root "$R90" --finalhash "$FINAL_SHA256" --reporthash "$REPORT_SHA256" --canonical-tree "$PROJECT/sources/preprints-tree.json"
```

The own verifier is read-only. It validates exact packet contents and permission modes, including packet root, rejects special/symlink/hardlinked payloads, and authenticates the complete canonical records and retained evidence. Removed acquisitions have metadata only. The external complete-tree bytes must match the fixed SHA256. Execution assumes the reviewed verifier code and ordinary local filesystem; this is not a hostile-code sandbox or race-proof protocol.

To replay the 18 disposable-copy controls inside the owned root:

```sh
python -B "$R90/packet/public/control_checks.py" --root "$R90" --finalhash "$FINAL_SHA256" --reporthash "$REPORT_SHA256" --canonical-tree "$PROJECT/sources/preprints-tree.json"
```

The runner first authenticates the original with those detached arguments. It compares all copied inputs before and after each verifier invocation and the whole original root before and after, excluding only its receipt and transient work directory. It refuses an existing .control-work directory. It writes integrity-results.json outside the seal and removes disposable copies. The receipt hash is separately reported. One baseline and17 expected rejections are artifact checks, never mathematical gates; this suite has no separate audit-denial probes. Parent integration and any independent review remain separate.
