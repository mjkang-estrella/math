# Parent integration contract

No actual manuscript-gate verdict or hash is supplied in this directory.
`gate.json` is the non-authorizing pending template. The assembler's default
publication path rejects it before creating a destination file.

After reading and authenticating the actual independent manuscript review,
the parent creates two **new** project-relative JSON records under
`frontier/campaigns/2026-10-14/kinetic-parent/`. Existing frozen records stay
unchanged. Both should have `manuscript` in their filenames; the disposition
must. A Markdown narrative can be retained separately by parent choice.

1. The **actual parent disposition** is a structured JSON assertion by the
   parent. Required fields are `schema` equal to
   `kinetic-manuscript-parent-disposition-v1`, `authority` equal to
   `parent integration`, `manuscript_verdict` equal to `PASS`, and
   `full_original_scope` equal to the JSON boolean `true`. These are
   requirements, not a statement that the current pending manuscript passed.
   It also contains `bound_manuscript`, `review`, `review_manifest`,
   `reviewer_record`, and `reviewer`, as defined below. Extra narrative and
   authentication details are allowed. The parent must have actually made
   this decision before supplying it.
2. The **actual integration config** has `schema` equal to
   `kinetic-release-gate-v1`, `state` equal to `integrated`, and the same five
   binding fields. It adds `parent_disposition` and `review_artifacts`.

`bound_manuscript` is exactly the three-entry hash object in the pending
template (`main.tex`, `output/pdf/main.pdf`, `outputs.json`), not a new build.
The review has exact path
`frontier/campaigns/2026-10-14/kinetic-manuscript-review-r1/review.md` and the
review manifest has the corresponding `outputs.json` path. `reviewer_record`
points to an actual provenance/identity file authenticated by that review
manifest. `reviewer` is a three-string object with keys `provider`, `model`
and `task_id`, filled from the actual completed review, not anticipated IDs.
The parent explicitly binds this identity to the reviewer record bytes.

Every file record (`review`, `review_manifest`, `reviewer_record`,
`parent_disposition`, and each `review_artifacts` entry) has exactly:

```json
{"path": "project-relative/path", "sha256": "actual 64-digit lowercase digest", "bytes": 123}
```

The displayed record describes the schema; its values are not usable hashes.
The review and reviewer record must be members of the review manifest with
identical hashes/lengths. Additional `review_artifacts` must also be explicit
review-manifest members. The manifest may use relative or full project paths;
membership is normalized and duplicates/traversal rejected. Choose the
actual author-owned review, validation, source/proof comparison, finite
controls and QA assets needed to inspect the review. Never select external
raw source papers or generated binaries. The review manifest itself can retain
historical references to excluded files; that does not include those bytes.

The assembler requires `--parent-disposition-sha256` separately from the
config. Obtain this hash from the parent's actual authenticated integration
record. A hash copied from an untrusted config alone does not establish parent
authority. This is an explicit trust anchor and consistency chain, not a
cryptographic signature system. The assembler checks the parent's actual JSON
and every file binding; it never parses verdict words from Markdown.

The caller must pass the actual config with `--gate`, leaving the pending
template unchanged. Parent disposition and selected review files are added
to the bundle only after successful authentication. The bundle manifest
records the actual config path and trusted parent hash. If review requests
manuscript changes, these frozen hashes cannot be used: create and review a
new freeze, then deliberately update the release bindings and inventories.

`outputs.json` here authenticates the preparer's files other than itself.
`allowlist.json` authenticates the selected 139 historical files. Parent-owned
new gate records enter through the separate checked config; no wildcard adds
the active reviewer directory. Verify those counts against the inventories
if a later preparation revision intentionally changes membership.
