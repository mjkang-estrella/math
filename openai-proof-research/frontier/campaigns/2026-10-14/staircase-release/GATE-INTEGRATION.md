# Actual final manuscript gate contract

No active manuscript-review file was consumed during preparation. `gate-pending.json` is non-authorizing. The parent must await the actual final `staircase-manuscript-review-r1` output, assess the full original scope and attribution requirements, resolve any repairs, authenticate reviewer provenance, and create a NEW disposition. If that process changes any frozen paper byte, stop and prepare/review a deliberate new freeze; this edition rejects hash substitution.

The JSON schemas document structure; `release_common.gate_records` additionally enforces actual files, manifest membership, hashes, lengths, normalized paths and the independent trust anchor. They implement consistency/integrity, not signatures or automatic mathematical judgment. Do not use a PASS substring or a model label as an approval.

Required actual parent disposition, under `staircase-parent/` with `manuscript` in the filename:

- `schema`: `staircase-manuscript-parent-disposition-v1`.
- `authority`: `parent integration`; `manuscript_verdict`: `PASS`; `full_original_scope`: boolean true; `required_repairs`: empty list.
- `bound_paper`: EXACT mapping from project-relative `main.tex`, `main.pdf`, `output-manifest.json` paths to the three SHA256 values in `gate-pending.json`. This asserts that the actual review and parent decision apply to these exact bytes.
- `review`: actual record for `staircase-manuscript-review-r1/review.md`; `review_manifest`: actual JSON manifest record under that review directory.
- `reviewer_record`: an ACTUAL review-manifest member bearing/bound to actual identity provenance. It may equal `review` if no separate identity artifact exists. Do not invent an identity file.
- `reviewer`: exactly nonempty `provider`, `model`, `task_id` strings, authenticated from completed review/orchestration evidence. `reviewer_identity_basis`: a nonempty explanation connecting that actual provenance and task to `reviewer_record` bytes.

Each record has exactly `path`, lowercase 64-hex `sha256`, nonnegative integer `bytes`. Paths are canonical POSIX project-relative names, with no absolute/traversal/backslash/empty/dot components, symlink components or duplicate normalized members. Manifests may be a list or have exactly one recognized `files`/`outputs` key; record paths may be review-relative or fully project-relative under the actual review. The review and identity must match exact manifest members; a self-hashing review manifest is rejected. Only explicitly selected additional actual manifest members are included. Forbidden reading-copy/cache/binary paths remain forbidden. The parent is responsible for substantive assessment and redistribution rights in any selected additional evidence.

After authenticating this disposition, obtain its digest independently of any proposed gate config. `bind_gate.py` reads that actual file, copies its actual review/provenance fields, checks all bindings and writes a new parent config exclusively. It neither creates nor infers a review verdict. Repeat `--artifact` for actual extra review members, never for duplicates of review/identity. The config uses `schema: staircase-release-gate-v1`, `state: integrated`, the same `bound_paper` and five review/provenance fields, plus actual `parent_disposition` and explicit `review_artifacts` (possibly empty).

Assembly and clean-extraction verification BOTH require `--trusted-parent-sha256`, recheck the actual parent record, all shared parent/config fields, the review/identity/additional manifest memberships, and the exact paper hashes. The config, disposition, review manifest and selected members enter the ZIP through these explicit records. The bundled copy of the trusted digest is a consistency record; it is not an independent trust anchor. The recipient should receive that digest (and preferably the archive digest) from the parent separately.

Preparation contains no fake approving reviewer identity or accepting parent disposition. Its temporary PREPARATION_ONLY archives test transport/extraction and hashes; production verification explicitly rejects their kind. The parent must perform the first real final-gate assembly and verification after actual PASS. This local packaging step still awards no campaign acceptance or count change.
