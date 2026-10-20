# Read-only reproduction

Inspect verify.py before executing it. Supply full SHA256s from the independent terminal handoff, not from a self-asserting local sidecar:

    python -B verify.py --root /absolute/path/to/t009p102-contribution-r1 \
      --final-sha256 FULL_FINAL_FROM_HANDOFF \
      --manifest-sha256 FULL_MANIFEST_FROM_HANDOFF \
      --report-sha256 FULL_REPORT_FROM_HANDOFF

MANIFEST.json covers every other file and directory, including scratch, protected evidence and controls. REPORT.md is outside that manifest and separately anchored. FINAL.json binds the manifest, outside report and original review prose and is externally anchored. The verifier only reads and prints. It rejects unsafe paths, duplicate JSON keys, symlinks, special files, multiply-linked regular files, missing/extra payloads, changed bytes/modes and mismatched detached anchors. The three outside files are regular single-link files checked by hash, not payload mode.

The retained private author copy keeps its original detached anchors. To independently replay its read-only verifier, run private/author-copy/verify.py with --root private/author-copy and the three original hashes recorded in REVIEW.md. It authenticates all27 pinned bodies against the complete13223-entry tree/Git blobs/SHA256. Its own documented limitations remain intact. Do not run the author controls writer in that retained sealed root.

controls/results.json records nine small copied preseal fixtures for this review's verifier: clean, modified prose, missing protected evidence, unexpected hidden file, symlink, mode change, changed outside report, wrong detached FINAL and forged reseal retaining old external anchors. Fixture trees are removed before the one production seal. These controls test artifact behavior, not mathematical correctness, substantiality, priority or acceptance. Their writer is retained for inspection; rerunning it in the sealed review would change the receipt and invalidate its manifest.

Private original-before/original-after and external-original observations establish the recorded before/after boundary only. Future mutable parent changes do not redefine mathematical input bindings and are not checked by the portable read-only verifier.
