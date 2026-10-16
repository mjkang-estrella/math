# Parent integration contract — corrected edition v2

`gate.json` is a non-authorizing pending template. The final focused review is expected under `../kinetic-manuscript-review-r2/`. The task name supplied by the parent is context, not an authenticated identity or completion record. This preparation did not read that active directory, anticipate its output hashes, presume PASS, or create a reviewer identity.

The real original review under `../kinetic-manuscript-review-r1/` is included and authenticated using its actual **outputs** schema. Its PASS binds only the original paper. It cannot satisfy this v2 gate.

## Required actual disposition

After the actual final review is complete, the parent must authenticate its bytes and evidence, resolve its findings, and make its own full-scope decision. If further paper changes are required, stop: this freeze cannot be accepted by substituting new files or old review hashes. Prepare and review a new edition deliberately.

The parent then creates a **new** JSON file under `frontier/campaigns/2026-10-14/kinetic-parent/` with `manuscript` in its filename. Required fields:

- `schema`: `kinetic-manuscript-parent-disposition-v2`
- `authority`: `parent integration`
- `manuscript_verdict`: `PASS`
- `full_original_scope`: JSON boolean `true`
- `manuscript_path`: `frontier/campaigns/2026-10-14/kinetic-manuscript-consolidation`
- `bound_manuscript`: exactly the four-entry object in this edition's `gate.json`, including `inputs.json`
- `review`: actual file record for `frontier/campaigns/2026-10-14/kinetic-manuscript-review-r2/review.md`
- `review_manifest`: actual file record for that directory's `outputs.json`
- `reviewer_record`: actual review-manifest member that the parent binds to the reviewer's identity/provenance
- `reviewer`: exactly three nonempty strings: `provider`, `model`, `task_id`, taken from the actual completed review and authenticated orchestration provenance
- `reviewer_identity_basis`: nonempty explanation identifying the actual provenance used, why it establishes that provider/model/task, and how it ties that identity to `reviewer_record` bytes

Extra parent narrative fields are allowed. These requirements are not a claim that a PASS exists.

Each file record has **exactly** `path`, `sha256`, `bytes`: a normalized project-relative path, actual lowercase 64-hex SHA256 and nonnegative integer byte length. No example hash or invented identity file is supplied here.

A separate identity file is **not required**. If none was delivered, `reviewer_record` can be the actual `review.md` or another actual manifest member. It may equal `review`. The parent must explicitly attest the identity-to-artifact connection using actual review text and/or completed-task provenance in `reviewer_identity_basis`. An unverified model label or a filename alone is insufficient. Do not fabricate a `provenance.json` to satisfy the interface.

## Manifest shapes and membership

The review manifest may be a list of records, an object with `files`, or an object with `outputs`. Exactly one recognized key is allowed in an object. Rows must have the exact record schema. Paths may be relative to the review directory or fully project-relative under it. Normalization rejects traversal, absolute paths, backslashes, ambiguous separators, foreign project paths, duplicate normalized members and malformed lengths/hashes. Duplicate JSON keys and self-hashing review manifests are rejected.

The review and identity member must match actual manifest rows byte-for-byte in path/hash/length. Additional selected review artifacts must each be a manifest member. They may include finite controls, source comparisons, validation and QA evidence, but never raw third-party sources, caches or generated Lean binaries. Historical manifests may mention omitted files without causing those files to be included. The parent is responsible for selecting only redistributable review evidence.

## Build the config without inventing records

After authenticating the disposition, obtain its SHA256 through the parent's trusted channel. The trust anchor must be independent of an untrusted config. The following helper reads that existing disposition, copies its actual identity and review bindings, checks the selected actual manifest members and writes a **new** config exclusively:

```sh
python3 -I frontier/campaigns/2026-10-14/kinetic-release-v2/bind_gate.py \
  --parent-disposition frontier/campaigns/2026-10-14/kinetic-parent/ACTUAL-manuscript-disposition.json \
  --parent-disposition-sha256 ACTUAL_INDEPENDENTLY_TRUSTED_SHA256 \
  --artifact frontier/campaigns/2026-10-14/kinetic-manuscript-review-r2/ACTUAL-ARTIFACT \
  --output frontier/campaigns/2026-10-14/kinetic-parent/ACTUAL-manuscript-config.json
```

`--artifact` is repeatable or may be omitted. Do not repeat `review`, `reviewer_record` or another selected artifact. The helper supplies no anticipated filenames except the contract's review/manifest locations, no verdict and no identity. It fails before writing if the disposition or any binding is invalid, and never overwrites a destination.

For manual config construction, use `schema: kinetic-release-gate-v2`, `state: integrated`, the same `manuscript_path`, `bound_manuscript`, `review`, `review_manifest`, `reviewer_record`, `reviewer`, `reviewer_identity_basis`; add `parent_disposition` (its actual record) and `review_artifacts` (an explicit list, possibly empty). Assembly independently validates the same contract; using the helper is optional.

Then use the README's assembly command, passing both the actual config path and independently trusted parent disposition hash. The parent disposition and config remain separate from frozen v2 machinery, and enter the eventual bundle only through the authenticated gate. `BUNDLE-MANIFEST.json` records the actual gate path and trusted hash. Preserve the pending preparation snapshot unchanged.

## Trust and validation limits

This is an integrity/consistency contract, not a cryptographic signature system or automatic mathematical referee. It checks the parent's explicit assertion and all file bindings; it never parses a PASS substring as approval. The parent must perform the substantive assessment and provenance authentication.

Preparation tests the pending/rejection boundaries, manifest parsers, real historical bindings, selected bytes, extraction and deterministic writer. A positive integrated end-to-end run cannot be truthfully performed before actual final review and parent disposition exist. No acceptance fixture or substitute reviewer identity was manufactured. The parent must perform that final integrated run and archive verification after its actual decision.
