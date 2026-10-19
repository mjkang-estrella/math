# Independent review authentication

Use the review's FINAL and outside REPORT SHA256 values supplied in the external handoff. Do not obtain purported trusted expectations from inside the packet.

```sh
python -B /path/to/t238b125-proof-r1/packet/public/verify.py \
  --root /path/to/t238b125-proof-r1 \
  --finalhash DETACHED_REVIEW_FINAL_SHA256 \
  --reporthash DETACHED_REVIEW_REPORT_SHA256
```

The verifier is read-only and network-free. It checks the detached FINAL/REPORT pair, exact packet file and directory membership and modes, hashes, copied author anchors and saved terminal handoff, complete canonical-tree identity, and the selected six source bodies against their canonical Git blobs. It does not import or run author code, execute diagnostics, re-evaluate the mathematical verdict, or assign contribution/count. Python's audit hook is a precaution, not an adversarial OS/native-code or concurrency sandbox.

The outside FINAL.json binds packet/MANIFEST.json and REPORT.md. The manifest binds all packet payloads, including this verifier, controls, review, reading limits, and selected private evidence. It excludes itself to avoid a circular hash. The outside copied-controls receipt, final-verification receipt and author-preservation receipt are separately anchored in the external handoff, not recursively included in FINAL.

To replay the independent controls, supply a new output directory name under this review root:

```sh
python -B /path/to/t238b125-proof-r1/packet/public/controls.py \
  --root /path/to/t238b125-proof-r1 --out fresh-controls \
  --finalhash DETACHED_REVIEW_FINAL_SHA256 \
  --reporthash DETACHED_REVIEW_REPORT_SHA256
```

This authenticates the original, then creates disposable copies only under the new output directory. Fourteen cases cover an unchanged copy; wrong detached anchors; changed/missing/extra payloads; an extra empty directory; symbolic and hard links; file and packet-root modes; and deliberately reanchored source, transport and verdict corruptions. The three reanchored cases use artificial test anchors, explicitly not the legitimate handoff anchors, to exercise deeper checks. Most ordinary mutations are rejected by enclosing hashes or the exact manifest. Copies are removed after each case; the receipt retains the observed reasons. A before/after inventory covers all preexisting review files and modes, excluding only the new controls subtree. Nothing writes into the author directory.

private/author-before.json records the author's pre-seal byte/mode inventory. The separate author-preservation receipt records the post-control comparison. This checks preservation during review packaging, not concurrent adversarial changes or access times. All retained third-party and authored evidence remains private under original rights.

No finite mathematical diagnostic is part of this verification. The correctness verdict is the independent reasoning in review.md at the full frozen scope; successful checks authenticate that reasoning's bytes, not its truth.
