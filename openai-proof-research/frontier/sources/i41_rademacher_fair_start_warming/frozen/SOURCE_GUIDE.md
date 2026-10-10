# Source provenance

The accepted upstream repository is `https://github.com/openai/math`, pinned
to commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Retrieval was on
2026-10-08. [upstream.json](sources/upstream.json) records the commit metadata.
All OpenAI mathematical theorem statements are taken as true at the user's
direction. A conditional theorem is used only with its stated hypotheses;
the instruction is not interpreted as making every conjectural hypothesis true.

The copied `sources/README.md`, `sources/CONTENTS.md`, and
`sources/overview.tex` are upstream documents, not this project's findings.
Their license is [sources/LICENSE](sources/LICENSE). The pinned catalogue
reports 719 manuscripts in 372 families; family numbering contains gaps.

## Exact sources used by accepted findings

[used-sources.json](sources/used-sources.json) records the paths, byte sizes
and SHA-256 hashes of 18 directly cited theorem-source files. The script
[fetch_used_sources.py](sources/fetch_used_sources.py) fetches them using the
immutable revision and rejects hash mismatches. Its `--verify-only` mode
checks local copies without network access. All 18 passed that check.

Files are restored under `sources/cache/verified/`. Downloads are ignored by
git; the small manifest and fetcher are committed. The source files provide
the actual statements and conventions; the proofs of our deductions are in
`findings/`. Full upstream Lean projects were not built. External classical
results have primary-source links in the findings and reviews, but are not
mirrored or included in this hash manifest.

## Exploratory cache and retrieval limitation

GitHub's recursive root-tree request returned 58,727 entries with
`truncated: true`, ending inside `lean/`. Absence from that response is not
evidence of an absent manuscript. The separate `preprints` subtree request
returned 13,223 entries with `truncated: false`. Both JSON listings and the
larger scout caches are ignored retrieval aids, not authoritative inventories
committed by this project.

The agents inspected relevant companion and consequence sections before
promoting results. This was a targeted check, not a full-text novelty audit
of all 719 manuscripts. The exact literature search limitations and prior
conditional formulations are recorded in the reviews.
