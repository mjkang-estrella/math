# TS132 independent scoped formal gate

Verdict: PASS_SCOPED_SUPPORT. Full TS132 formalized: false. See review.md for exact contracts, exclusions, independence disclosure and trust boundaries. This package changes no campaign count and authorizes no publication.

Authenticate this sealed review with an independently supplied manifest hash:

```sh
python -B verify_review.py --anchor EXTERNAL_MANIFEST_SHA256
```

The command is read-only and checks exact payload/directory membership, byte identities and internal evidence consistency. It does not rerun Lean or replace the human audit. Add `--dependency-parent /absolute/path/to/campaign` to authenticate all five original packets with their fixed anchors. Private dependencies are intentionally not redistributed; without that flag historical input identities remain receipts rather than live rechecks.

For fresh execution, copy this package to a new working directory, then run the unchanged helpers there with explicit absolute paths:

```sh
python -B work/rebuild.py --cache /absolute/path/to/pinned/.lake/packages --output logs/replay-build
python -B work/mutations.py --cache /absolute/path/to/pinned/.lake/packages --output logs/replay-mutants
```

Use Lean 4.34.1 and the exact lake-manifest.json dependency pins. The helpers accept `--lean` for the executable if the recorded local default is unavailable. They check dependency revisions read-only and use a fresh temporary support build. Cached dependency objects and the Lean executable remain trusted. The complete original command receipts are in work/logs; the author helper's `independent_audit=false` field is intentionally unchanged and is not this review's verdict.

For the runner failure control in that working copy, run `python -B work/checked_run.py --log-prefix logs/replay-runner -- python -c 'print("SOME FAIL")'`; the child exits zero and the wrapper must reject with exit one. The actual recorded invocation/output is retained in work/logs/runner-control. All six mutant rejection logs were inspected at proof goals. Original reports and helper provenance are retained; no task-source object or dependency object is bundled.

In a disposable working copy, `python -B check_integrity_controls.py --output replay-controls.json` exercises positive, wrong-anchor, changed, missing, extra-file, extra-empty-directory and symlink cases. Adding replay evidence changes that copy’s sealed membership; preserve the original package read-only. The verifier and this control helper are identical original review code in the two gate packages.
