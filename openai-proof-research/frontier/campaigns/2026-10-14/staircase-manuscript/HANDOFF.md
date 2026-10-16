# Resumed manuscript implementation handoff

Completed only within `frontier/campaigns/2026-10-14/staircase-manuscript/`. The interrupted task's input snapshots, copied code, and expected results were reused and authenticated. No restart of the candidate proof or change to frozen source bytes was necessary.

The six-page `main.pdf`, `main.tex`, and `references.tex` give the full original theorem and self-contained proof. Section 3 proves the exact equality of the coordinate-functional formula and the q/content projection. Section 4 preserves the square-deficit plus nested-palette proof and ordered signs, with unit coefficient +1. The final proof establishes splitting over Z and arbitrary nonflat base change directly. Bryant–Kovács are credited as a field-level antecedent; their injectivity argument is not assumed over Z. All required attribution conditions are answered in `attribution-response.md` and located in the source map.

Validation completed:

- All 41 input entries and all 13 pinned contract slices match their frozen hashes. The frozen candidate, proof review and contribution review match the exact hashes in the brief.
- Both previously independent checker copies run successfully in temporary copies. Complete output bytes equal their frozen expected results. This is reproduction, not a new independent review. The product-coordinate checker covers m <= 5; the orbit checker covers all 727 group elements at m <= 3.
- A new bounded interface control compares both retraction formulas on 512 basis triples and six group elements, for 3,072 comparisons, with all assertions passing. It is implementation support only.
- Tectonic 0.17.0 builds copied sources successfully with zero overfull boxes and no unresolved references. Poppler renders all six pages, and every page has been visually inspected. Receipts and per-page hashes are retained.
- The public archive is constructed from an explicit allowlist. It excludes the entire inputs tree and every third-party primary PDF/TXT reading copy, while retaining source links and exact provenance hashes. Its contents and payload hashes are verified separately from the complete internal audit bundle.

`output-manifest.json` and `SHA256SUMS` freeze the full local handoff; `public-manifest.json` freezes the public payload. The archive is prepared, not uploaded or published. No shared edits, staging, commits, subagents, acceptance action or campaign-count change occurred in this implementation.

The original candidate has a full proof PASS and a conditional contribution verdict; those are provenance only and do not review this manuscript. Independent manuscript review and parent formal-coverage integration are still pending. No full Lean proof or formal certificate exists in this package, and none is claimed. `formal-scope.json` is an honest placeholder for that separate work. This task does not accept the staircase result.
