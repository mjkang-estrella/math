# Source contracts for B8C

Myeongjin Kang; no affiliation. 2026-10-16. Prose CC BY 4.0.

Upstream: openai/math at commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Paths come from `sources/preprints-tree.json` (complete listing, 13223
entries, truncated = false; SHA256 eeecc1da…dc5e09b). All files were
retrieved from pinned raw URLs. Every retained file's Git blob SHA-1
equals the tree entry; the per-file record is `inputs/pinned-records.json`.

## Family 156

Directory: `preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/`

| file | blob sha1 | reading extent | labels used |
|---|---|---|---|
| README.md | 0e86c962… | full | none |
| build/main.tex | 7f8e2cd3… | full | section order only |
| build/preamble.tex | e49fd1bb… | full | none |
| build/references.bib | ce92bf89… | full | none |
| build/sections/introduction.tex | 3c1266ab… | full | thm:main (statement) |
| build/sections/geometry.tex | be19e1b7… | full | lem:projector-geometry, def:admissible, lem:cover-to-map |
| build/sections/extension.tex | 039529b7… | full | lem:positive-extension, lem:signed-extension |
| build/sections/topology.tex | b68e9e52… | full | thm:label-bound, thm:equality-complex |
| build/sections/six-labels.tex | 002ebac9… | full | screening only |
| build/sections/ten-labels.tex | 6380e0c5… | full | screening only (thm:no-ten-labels) |
| build/sections/conclusion.tex | b396e98c… | full | cor:higher-dimensions (statement) |
| build/figures/*.tex (3) | see records | retained, not read | none |
| paper.pdf | 0d18ffb4… | not retained, not read | none |

## How the candidate depends on the source

**No source theorem is a proof input.** The candidate re-proves the
Hermitian versions of the three lemmas whose method it borrows:

- candidate Lemma 3 corresponds to lem:cover-to-map;
- candidate Lemma 4 corresponds to lem:positive-extension (continuity,
  trace and support parts only);
- candidate Lemma 5 corresponds to lem:signed-extension (odd map and
  ℓ^1 norm only).

The proofs are adapted to C^3 and use continuous partitions of unity
instead of smooth ones. The smoothness, subspace and degree parts of
the source lemmas are not used.

The source's real-case results (thm:label-bound, thm:equality-complex,
the six- and ten-label sections, thm:main and cor:higher-dimensions)
motivated the target and are cited only for context. If one of them
were false, no step of the candidate would change.

External standard facts used: the Borsuk–Ulam theorem (no odd continuous
map S^n → S^{m−1} for m − 1 < n), continuity of the PSD square root,
compactness, and Cauchy–Schwarz/Bessel.

## Other inputs

- `inputs/primary/kalai-1505.04952v1.pdf` (SHA256 70066d86…f2f4dad,
  271036 bytes). Extent: Section 2.3 (read in screening) and Sections
  2.4–2.6 of the retained bytes. Context only: real tensor embedding and
  Problem 2.13. Not a proof input.
- arXiv:2608.12561 (dimension-63 counterexample) and arXiv:1410.5862
  (SIC classification in CP^2) were seen only as search results. Neither
  was retained, read or used.
- `inputs/context/`: snapshots of AGENTS.md, the brief, tasks.json and
  upstream.json (hashes in `unchanged-source-receipts.json`).
- `inputs/lr-r2-authentication.json`: the LR-r2 package was authenticated
  against the externally supplied seal 06c49552…8c3e4 (34 files, 6
  directories) before any reliance. In the end the candidate uses nothing
  from LR-r2.
