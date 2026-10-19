# T096N126 correctness R1 packet

`review.md` is the self-contained mathematical review: **PASS original theorem without repairs**, conditional on the stipulated source and accepted I38 inheritance. `reading-provenance.md` states actual reading limits and public/private rights. `handoff.md` is also copied exactly to the outside `REPORT.md`.

`MANIFEST.json` authenticates exact files, byte sizes, SHA256 and directory names under `packet/`, excluding only the manifest itself. Nonregular entries are rejected. Permission modes, hardlink counts and timestamps are NOT bound. `FINAL` outside the packet contains SHA256 of the EXACT manifest bytes, not the digest of the FINAL text file. The separate outside report has its own detached digest. Use the values supplied in the final handoff as external anchors; reading an anchor from a possibly modified packet is not independent authentication.

From the repository root, run the OWN read-only verifier:

```sh
python -B frontier/campaigns/2026-10-14/t096n126-proof-r1/packet/public/verify.py \
  --root frontier/campaigns/2026-10-14/t096n126-proof-r1 \
  --project-root . --expected-final REVIEW_MANIFEST_SHA256 --expected-report REVIEW_REPORT_SHA256
```

It checks this packet and outside report,28 complete immutable input snapshots against actual originals, the entire80-file actual author root against the saved baseline, the author packet against the externally supplied author anchors, freeze records, the full nontruncated canonical tree, four selected pinned bodies' SHA256/Git identities, and the first four inherited history copies against their actual bodies. It never runs author code. It installs a Python audit hook denying writable opens, mutation, process creation and network connections; it emits JSON to stdout only. Invoke with `-B` to prevent interpreter bytecode caching.

Disposable controls use the same external anchors:

```sh
python -B frontier/campaigns/2026-10-14/t096n126-proof-r1/packet/public/controls.py \
  --root frontier/campaigns/2026-10-14/t096n126-proof-r1 \
  --project-root . --expected-final REVIEW_MANIFEST_SHA256 --expected-report REVIEW_REPORT_SHA256
```

The control runner copies the ENTIRE sealed review packet afresh for each case, never hardlinking originals. All temporary files remain under this review's `work/`. It tests pristine acceptance; changed, deleted, additional and renamed payloads; extra empty directories; symlinks; manifest changes; a coordinated reseal against the old external anchor; changed outside report/FINAL; wrong external anchors; and the intentionally unbound permission-mode/hardlink-count behavior. It verifies originals before and after and confirms each verifier run leaves copied bytes unchanged. Results and their SHA256 are outside the sealed packet in `work/controls-result.json` and `.sha256`; they are not self-included in the manifest. Full disposable copies are deleted after each case.

These are integrity controls, not analytic proof tests or contribution gates. Mathematical justification is in the review. No numerical test is presented as evidence for the theorem.

Public reviewer prose: CC BY4.0 under the project convention. Original Python code: MIT. Private snapshots and evidence retain original rights and must not be included in public redistribution. Parent integrates; this packet authorizes no publication, formalization, shared-index edit or contribution decision.
