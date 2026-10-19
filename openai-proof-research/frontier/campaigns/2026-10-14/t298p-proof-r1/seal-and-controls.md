# Seal and copied controls (T298P proof review r1)

`MANIFEST.json` lists the SHA256 of every other file in this directory. It also records the author anchor and the verdict field. Its own SHA256 is reported externally, in the reviewer's return message to the parent, and is not stored in this directory.

`verify.py` is read-only and writes nothing. Run it from any working directory:

    python3 -I verify.py --anchor <EXTERNAL_MANIFEST_SHA256> --repo /home/mj-kang/Documents/Dev/math/openai-proof-research

Optionally pass `--author-dir` to point at a copied author packet.

## What the verifier checks

- Exact membership of this directory, with every entry a regular file and no symlinks.
- Every payload hash.
- Seven external author anchors: the author MANIFEST, candidate, scope-freeze, comparison, matched-volume, unconditional-score and stress-checks.
- The recorded author anchor and the verdict field.

## Copied controls

The controls run only on copies under `/var/tmp`. They never mutate this packet or the author packet. Each negative case must fail with the reason listed below:

| Case | Expected reason |
|---|---|
| positive (anchored) | PASS |
| wrong external anchor | `external manifest anchor` |
| altered review.md byte | `payload review.md` |
| missing reading-limits.json | `exact public membership` |
| extra file | `exact public membership` |
| symlinked extra file | `regular file` |
| altered author candidate copy (`--author-dir`) | `author anchor candidate.md` |
| altered check output byte | `payload checks/outputs/recovery_simulation.json` |

Control results are written outside the sealed packet, to `/var/tmp/t298p-proof-r1-controls.json`.

These checks authenticate identities only. They are not evidence for any mathematical claim.
