# Reading limits and access record

## 1. Pinned upstream (commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb)

Every retained source body was fetched from its pinned raw URL and matched by size and Git blob SHA1 to its full record in the complete 13223-entry `sources/preprints-tree.json`. The records are in `private/canonical.json`. `public/fetch.py` is the acquisition program.

Source: *The Euclidean plane is not five-colorable* (September 23, 2026), `build/`.

- Read in full: `sections/introduction.tex`, `sections/spectral.tex`, `sections/transfer.tex`.
- Read in part: `sections/rigidity.tex`, lines 320–618 (Følner averaging, `eq:source-9`, `lem:rigidity-general-position`, `lem:rigidity-capped-residues` and the completion of `thm:rigidity`). Lines 1–319 (the compact tower) were not read. Their field-generality is therefore unverified, as `plane-coloring-158.md` states.
- Retained for structure only: `main.tex` (section inputs).

Six further files were acquired and then removed after keyword search only: `README.md`, `figures/proof-flow.tex`, `sections/angular.tex`, `sections/interfaces.tex`, `sections/palettes.tex` and `sections/transitions.tex`. They are not relied on. Their paths, sizes and SHA256 values are kept in `private/context/removed-acquisitions.json`, but they have no canonical records. All source labels cited in the notes are in the retained files. The catalogue (`sources/CONTENTS.md`) was used for navigation only.

## 2. Primary literature

- **Davies, arXiv 2610.12301v1** and **Koshelev–Kupavskii–Voronov, arXiv 2610.18907v1**: the text extractions retained by structural r20 (`fresh-structural-discovery-r20/private/primary/*.txt`) were read in place and are bound by SHA256 in `private/context/input-bindings.json`. Davies: lines 1–320 (introduction, Theorems 1.1–1.3 and the remark on Bukh's conjecture) and lines 2270–2299 (Lemma B.1 neighbourhood), plus lines matched by a search for "Bukh". KKV: lines 1–130 (introduction) and 805–904 (Sections 7–8, Lemma 7.1, Corollary 8.2, the density sum (16)). Proofs beyond those extents were not read. These are external results, not stipulated pinned sources.
- **Ambrus–Csiszárik–Matolcsi–Varga–Zsámboki, arXiv 2207.14179v3**: abstract only, from arXiv API metadata retained in `private/primary/acmvz-arxiv-api.xml` with `private/primary/receipt.json`. The same query returned Ruhland 2408.10076v4, whose abstract records Croft's 0.22936 lower bound. The bounds m_1 <= 0.2470 and m_1 >= 0.22936 are used only as cited headline values.
- **Bukh** (measurable multi-distance theorem and the conjecture on algebraic conditions) and **Furstenberg–Katznelson–Weiss**: cited only through Davies's statements or as classical background. They were not opened.

## 3. Project history

Copied to `private/history/` and bound to their originals (`private/history/records.json`). All were read in full:

- r130: outside REPORT, public report, `ramsey-170.md`, `unit-distance-167.md`, `other-screens.md`, `reading-limits.md`, and the r130 parent intake.
- r116: `screens-157-186.md` and the r116 parent intake.
- r20: `status.json`, `original-scope.md`, `candidate.md`, `reading-and-provenance.md`.

The r44 and I22 notes on family 157 are cited only through r116's account and the search receipt. They were not opened in this round.

## 4. Searches

`private/search/*-paths.txt` are path-only ripgrep receipts over the project notes, with this round's root excluded. They cover three pattern sets: plane colouring and chromatic number of the plane (659 paths), Hadwiger / list and correspondence colouring (1143) and multi-distance or distance-set colouring (58). Most hits are metadata copies, catalogue copies and copied source bodies. I filtered them to authored `.md`/`.json` notes and opened the operative hits listed above. A hit is not a semantic read, and a missing hit is not evidence of absence.

## 5. Computation

No finite computations or numerical checks were run. The bounds 4.048 <= chi_f(R^2) <= 4.360 are hand reciprocals of the cited headline values. All calculations in the public notes are prefreeze feasibility work, not certified proofs.

## 6. Family-level history search

Before choosing a family, candidate families outside the CLOSED list were compared by counting operative prior notes found by family-number and title searches over `frontier` campaign and iteration notes. That count was navigation only and was not retained as a separate file. The receipts in Section 4 are the retained evidence for the 157 and 158 history.
