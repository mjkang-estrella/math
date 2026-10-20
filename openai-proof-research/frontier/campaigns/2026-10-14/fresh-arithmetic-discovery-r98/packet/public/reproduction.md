# Reproduction

Run from the repository root. Take `FINAL_SHA` from the parent handoff (the detached FINAL anchor); it is not stored in this packet. Take `REPORT_SHA` from `FINAL.json` and confirm it against the handoff.

```sh
R=frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r98
python3 -B $R/packet/code/verify.py --root $R --tree sources/preprints-tree.json \
  --final-sha256 "$FINAL_SHA" --report-sha256 "$REPORT_SHA"
python3 -B $R/packet/code/controls.py --root $R --tree sources/preprints-tree.json \
  --final-sha256 "$FINAL_SHA" --report-sha256 "$REPORT_SHA"
```

- **Verifier.** Read-only, enforced by an audit hook. It checks:
  - the detached FINAL and REPORT anchors;
  - the files bound by FINAL (manifest, verifier, controls, public report) and the preprints-tree SHA256;
  - the exact packet file and directory set with sizes, modes and SHA256 values, with no symlinks and no hard links;
  - every retained and removed pinned source record against the complete preprints tree (Git blob, size, raw URL) and against `public/fetch-log.jsonl`;
  - each retained source body (Git blob and SHA256), and that removed sources have no local copy;
  - each primary file against `public/primary-register.json`;
  - each history copy against `public/context-register.json`;
  - that no private file is unregistered, and `status.json`.
- **Controls.** Seventeen cases run the unchanged verifier on transient copies under `$R/control-work`, which is removed afterwards. The baseline must pass and every tampered copy must fail. The author root must be unchanged. The script rewrites `$R/integrity-results.json`.
- `packet/code/fetch_pinned.py` is the author-side fetch script; it writes files and is not part of verification.

These are artifact checks only. They are not mathematical gates.
