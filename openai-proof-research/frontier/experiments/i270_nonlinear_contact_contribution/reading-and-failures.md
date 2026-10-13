# I270 read extents, search log and execution limits

2026-10-12. Completed independent CONTRIBUTION review. **SUBSTANTIAL** for the full I249/I253/I263 limit as one prospective finding. No correctness verdict, acceptance/count change, subordinate run, or pending task.

## Assigned inputs read in full

- `AGENTS.md` and `sources/upstream.json`.
- `frontier/experiments/i263_nonlinear_contact_lower_bound/analysis.md`, all 280 lines, including Sections 1–10. SHA256 matches `d02db6dfe8b65bba3196baf2cd8de6eb4dec1ce13084696c9fe81ed2aee3fc95`.
- `frontier/iterations/i263-nonlinear-contact-lower-bound.md`, complete report.
- I263 `reading-and-failures.md`, `input-authentication.json` (all 312 lines), and `frontier/sources/i263_nonlinear_contact_lower_bound/literature.md`, complete. Initial combined-output truncation was repaired by separate reads; the full authentication JSON was read in two contiguous chunks, and the read log/literature were separately reread.
- `frontier/experiments/i249_geometric_analytic_discovery/analytic-attempt.md`, all 134 lines, including the original explicit unresolved verdict. SHA256 matches `ef588588ace48958cc6f3fad4af84d01c52198ea4bff10a1e3a890cd86772413`.
- `frontier/iterations/i253-contact-recovery-parent.md`, complete recovery.
- `frontier/sources/i249_geometric_analytic_discovery/literature.md`, complete comparison/provenance record.

No live I269 content or other live sibling output was read. No shared acceptance ledger or giant thread/history replay was opened. Initial discovery used filename listings filtered to I249/I253/I263.

## Catalogue and primary source extents

`sources/CONTENTS.md`: full family-354 block, lines 8608–8623, plus keyword matches for torus/isoperimetry. An initial whole-catalogue command produced truncated output; unrelated visible head/tail text was incidental and does not justify a full-catalogue read claim. `sources/preprints-tree.json`: matching family-354 path entries; one bounded displayed window included adjacent family paths, not used. No truncated root-tree cache was used.

All primary excerpts retained in the assigned I270 source directory were fully read:

- Pinned 354 entry `paper.tex`, `sections/preliminaries.tex`, `sections/geometry.tex`, `sections/sections.tex`, `sections/nesting.tex`, and `references.tex`: each entire file. The first four were copied from already authenticated I249 excerpts and freshly compared byte-for-byte with the pinned raw URLs; all match. Nesting and references were freshly retrieved from pinned raw URLs. No claim to reading every included manuscript file, figures, or numerical appendix.
- AFM author-final PDF: pages 3–4, 7, 22, 34–35, each entire extracted page. Pages 3–4 were retained separately from the old multi-page excerpt. An initial local read also displayed the beginning of page 18 through its Step 1 setup; it is incidental partial text, not a complete theorem-proof reading. Theorem 4.2 is stated without proof in the read source. Neighboring Proposition 2.7 and Theorem 4.3 fragments are not fully read proofs or premises.
- ABLW v1 PDF: pages 1–9 and 25–31, each entire extracted page. This includes the complete equality-case proof of Theorem 2.2, complete Proposition 4.4 proof, complete statement and presented proof sketch of Theorem 4.5, references, and page-31 figure caption. The page-9 Lemma 2.3 proof fragment and page-25 preceding proposition fragment are not treated as complete proofs. Pages 10–24 and cited dependencies were not read.
- ABLW v4 HTML: complete Section 4.4, retained with mathematical alttext. The preceding Section 4.3 statement/proof-sketch window was inspected online; it is not a full-paper read. This corrects the introduction's inconsistent second-Gamma-limit label and checks a later version of the closest contact-selection comparison.
- CLM planar-cluster repository PDF: pages 1–6, entire extracted pages. Initial combined output truncated the end; lines 235 onward were separately reread, completing pages 5–6. Theorem 1.5's complete statement is read. The theorem proof, appendices, and three-dimensional companion are not read.
- Lawlor arXiv:1212.4580v1 PDF: pages 1–4, entire extracted pages, including Theorem 8.1 statement. Later definitions/proof not read.
- Choksi–Sternberg 2007 author PDF: pages 1–6, entire extracted pages. This includes the local Jacobi expression, the stated nonlocal second-variation formula and second-order volume-preserving perturbation definitions. Full Theorem 2.6 proof not read.
- Choksi–Sternberg 2006 publisher PDF: pages 1–5 and 8–10, entire extracted pages. Page 3 contains an embedded-source text overlay; that block is not used as a premise. Theorem 4.1 statement and its presented proof are complete; the page-10 final conjecture setup is a fragment, not a complete classification theorem.
- Milman arXiv:2403.06602v3 HTML: complete Section 2.1, including the full presented proof sketch of Proposition 2.5 and the full Corollary 2.8 proof. Retained text preserves source mathematical alttext. Introductory online lines 48–97 and incidental neighboring material were inspected; later sections/appendix not fully read.

Primary landing pages and Choksi's publication index were navigation/version aids. Raw full PDFs/HTML were streamed for SHA256 provenance only; their unread complete contents were not retained as source artifacts. No new page rendering was needed or claimed.

## Exact bounded queries

The five web-search batches used these seventeen queries:

1. `"nested" "perimeter" "contact" second order isoperimetric`
2. `"core shells" "regularity" isoperimetric surface tensions`
3. `"ball" "tube" "torus" "contact" isoperimetric`
4. `isoperimetric clusters triangle equality surface tensions regularity nested sets`
5. `isoperimetric second order asymptotic tangency obstacle perimeter spheres cylinder`
6. `core shells double bubbles Alama Bronsard Lu Wang 2212.06381`
7. `Cicalese Leonardi Maggi improved convergence clusters 2016 pdf`
8. `Morgan immiscible fluid clusters 1997 pdf surface tension`
9. `"isoperimetric" "contact" "second-order" nested`
10. `Choksi Sternberg first second variations nonlocal isoperimetric problem 2007 pdf`
11. `Gary Lawlor Double bubbles immiscible fluids Rn arxiv`
12. `"nested" "perimeter" "quasiminimizers"`
13. `"contact" "isoperimetric" "asymptotic"`
14. `Choksi Sternberg periodic phase separation 2006 pdf`
15. `site.math.mcgill.ca choksi Sternberg periodic phase separation pdf`
16. `"second order" "contact" perimeter obstacle Gamma convergence`
17. `"ball" "cylinder" "nested" isoperimetric sharp`

Secondary portals, ResearchGate, conference snippets, unrelated packing/contact mechanics/quantum papers, and an unverified recent liquid-phase-cluster lead were not mathematical premises. The relevant leads were followed to arXiv, author/repository manuscripts, or publisher text. No external comments or messages were posted. No exhaustive citation chase or worldwide novelty certification is claimed.

## Retrieval and read failures repaired

Some initial combined tool results truncated source/authentication text. The required original analyses were read in dedicated untruncated outputs; I263 authentication was read in contiguous chunks; CLM's tail was separately read. A first HTML extraction attempt failed with `ModuleNotFoundError: No module named 'bs4'` after the authorized source copies had completed. No package was installed. A standard-library HTMLParser extraction then retained the complete Milman and ABLW sections, which were read fully. No failed retrieval remains necessary to the verdict.

The source record does not hide shortcomings: AFM cites classical regularity instead of proving Theorem 4.2 there; several companion arguments are explicitly proof sketches; broader referenced results were not independently read. These limits are stated rather than filled with claims from snippets.

## Runtime and write scope

Live own-thread configuration confirms provider `codex`, model `gpt-6.1-sol`, `reasoningEffort=high`, `serviceTier=default` (Standard). The catalog's provider-default reasoning entry is not substituted for the own-thread high setting. These are configuration observations, not independent billing attestation. No model switch or delegation occurred.

Only the assigned I270 review, experiment records, literature record and fully read primary excerpts were written. Retrieval/text extraction, mathematical reasoning, artifact authoring and provenance hashing were performed. No research code, tests, numerical scans, subagents, live sibling-content reads, shared edits, staging, commits, publishing, snapshots or public communications occurred. The small Python invocations served copying, primary-text extraction and authentication only. All work stayed inside this project; no pending task remains.
