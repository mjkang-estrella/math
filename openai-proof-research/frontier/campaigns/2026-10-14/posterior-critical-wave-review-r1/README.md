# PCW independent review, round 1

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code
(`verify.py`) MIT. Third-party files under `inputs/` keep their own rights
and are retained privately for reading only.

Verdicts: mathematics **PASS_FULL_PCW**; contribution **TECHNICAL**.
Counted=false; campaign 4/10.

| path | role |
|---|---|
| review.md | proof review, P1–P5, verdicts, optional clarifications |
| operation-comparison.md | P6 operation-level contribution comparison |
| source-reading.md | exact reading extents, retrievals, searches |
| status.json | machine-readable status |
| verify.py | read-only verifier; requires the external seal anchor |
| receipt-after.json | unchanged-input receipt after review writes |
| manifest.json | exact files, directories, roles, sizes, SHA256 |
| seal.json | detached seal over manifest.json (its SHA256 is reported externally) |
| inputs/author/ | byte copies of authenticated author files, incl. immutable original-scope.md |
| inputs/pinned/ | byte copies of the four pinned TeX interfaces used |
| inputs/parent/ | review and original briefs, parent records (verifier stored as text) |
| inputs/context/ | AGENTS.md, upstream.json, internal ledger snapshot |
| inputs/primary/ | reviewer-retrieved primary bodies |
| inputs/receipt-before.json | receipt of external fixed inputs before review writes |

Run: `python3 -B verify.py --anchor <seal sha256>` (add `--controls` for
mutation controls in a temporary copy; `--live` to re-hash the external
fixed inputs in the repository). Verification is integrity only.
