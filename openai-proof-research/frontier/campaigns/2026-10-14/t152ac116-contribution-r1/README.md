# Sealed original contribution review — T152AC116 r1

Read `review.md` and `reading-limits.md`. Verdict: TECHNICAL conditional on correctness. No correctness PASS, priority, eligibility, formal, manuscript, release, acceptance, finding-number or count certification is made.

Original review prose is at the root; original verification code and factual receipts are under `public/`. Third-party PDF/text material and historical reading evidence are under `private/`, under their original rights. They are not public originals and must not be redistributed as original review writing. Original review prose: CC BY4.0; original review code: MIT; this does not relicense any input.

The manifest inventories every file except itself, all directories and permission modes. Its trust anchor is the DETACHED SHA256 in the external review handoff. Never substitute a digest freshly computed from an untrusted manifest as an independently supplied anchor.

From the project root, set REVIEW to this directory, AUTHOR to the immutable author root and ANCHOR to the external review-manifest digest. Then run:

    python -B "$REVIEW/public/verify.py" --review "$REVIEW" --reviewmanifest "$ANCHOR" --author "$AUTHOR" --workspace "$PWD"

The verifier requires that detached anchor, binds all six supplied author/frozen/proof identities, checks the author exact packet inventory and FINAL/freeze bindings, the full author65-file snapshot, all19 canonical source blobs, four primary pairs and the anchored complete13223-entry tree. It writes nothing. It uses no git command or network. File/directory membership, modes, lengths, hashes, symlinks, hardlinks and special files are checked.

`public/controls.py` runs all mutations on disposable copies under `private/work/` and removes them. A final sealed replay uses the same arguments plus `--check-record`; it compares its outcomes with the sealed receipt without editing that receipt. Author22 copied controls are recorded separately in `public/author-controls.json`. Integrity establishes identity only.
