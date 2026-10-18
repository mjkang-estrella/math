# T027O contribution review r1: checkpoint

Status: complete and sealed. Verdict in `review.md`: SUBSTANTIAL (moderate
strength) for the complete unchanged T027O scope, with four required credit
objections (review §7). Not a proof verdict.

Directory contents:

- `review.md`: verdict and operation-level reasons.
- `reading-limits.md`: exact reads, unread material, what could change the
  verdict.
- `author-verification.json`: anchor checks, author verifier and control
  results, independent source-blob comparison.
- `history-search.json`: project-history and external searches.
- `primary-receipts.json`: sizes and SHA256 of retrieved comparator files.
- `private/primary/`: retrieved third-party texts (git-ignored by
  `.gitignore`; included in the sealed inventory).
- `verify.py`: read-only verifier; requires the external SHA256 of
  `manifest.json` as its only argument.
- `controls.py`: mutation controls run on fresh copies under `/var/tmp`.

The manifest anchor is reported outside this directory, in the reviewer's
final message, because a file cannot contain its own seal. Control results
were produced after sealing and are likewise reported there.
