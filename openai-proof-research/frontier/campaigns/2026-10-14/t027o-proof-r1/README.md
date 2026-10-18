# T027O independent proof gate, round 1

The verdict, rederivation, dependencies, editorial items and read limits are in review.md. The final manifest SHA256 is reported outside this directory. Verify with:

    python3 -B verify.py EXTERNAL_MANIFEST_SHA256
    python3 -B self-controls.py EXTERNAL_MANIFEST_SHA256      # copies under /var/tmp only; prints results

Replay the reviewer evidence. Both commands print JSON identical to the stored files. Do not redirect output into this directory while verifying.

    python3 -B reviewer-diagnostic.py        # = reviewer-diagnostic.json (finite-field diagnostics, not proof)
    python3 -B author-packet-controls.py     # = author-packet-controls.json (author anchors, canonical comparison, /var/tmp copied controls)

No third-party body is stored here. Nothing here certifies proof, contribution or novelty by hash or finite computation.
