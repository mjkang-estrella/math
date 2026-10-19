# Reading limits and access record

## Pinned upstream (commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb)

Every retained source body was fetched from its pinned raw URL and matched by size and Git blob SHA1 to its full record in the complete 13223-entry `sources/preprints-tree.json`. The records are in `private/canonical.json`. `public/fetch.py` is the acquisition program.

Read in full:

- 170: `Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers.../sections/00-introduction.tex` and `06-conclusion.tex`.
- 171: `The-hypercube-Ramsey-number-has-linear-order.../sections/01-introduction.tex` and `02-reduction-and-notation.tex`.
- 160: `Quantitative-Superexponential-Bounds-for-van-der-Waerden-Numbers.../sections/01-introduction.tex` and `02-setup.tex`.
- 164: `Monochromatic-finite-sums-and-products.../sections/01_introduction.tex`.
- 167: `A-power-saving-for-planar-unit-distances.../sections/00-introduction.tex`.

Ten further files were acquired and then removed unread or only keyword-searched: the 170 foundations section and main.tex; the r(5,t) companion's introduction, which was keyword-searched for "r(4"; its paper.tex, upper-bound, final-conversion and predictor-statement files; the 171 regime guide; the 160 counting section; and the 164 framework section. They are not relied on. Their paths, sizes and SHA256 values are kept in `private/context/removed-acquisitions.json`, but they have no canonical records. No proof section of any source beyond those listed was read. All source statements used are the displayed theorem statements and the proof passages in the files read in full. The catalogue (`sources/CONTENTS.md`) was used for navigation only.

## External primaries

None were retrieved. Classical results cited in the notes (Guth–Katz polynomial partitioning, unit-circle Szemeredi–Trotter, the girth/independence ratio of random regular graphs, the cube embedding cost of grids) are standard background. They are not new source reads and have not been checked against primary bodies in this round. Statements about Mattheus–Verstraete, Bradac and AKS are taken from the pinned source introduction.

## Project history

Copied to `private/history/` and bound to their originals:

- Read in full: r129 outside REPORT, public report, weighted-rank feasibility, L1-embedding feasibility, other screens, reading limits and the r129 parent intake; r42 report; r113 parent intake and `screen-176.md`; r114 `screen-171-247.md`.
- Read in part: r35 `mixed164.md` (first 2500 bytes); r81 `working.md` (lines matched by family-number search); `proposals/combinatorics.md` (summary table and lines 118–150); the i39 frozen `F002-clique-free-edge-genus.md` (lines matched by Ramsey search).

The r32 and r48 cube notes are cited only through r114's account. They were not opened.

Arithmetic r95's `work/family-history-counts.txt` was read early, for navigation only. That round later removed its work directory, so no copy or hash could be retained. `private/context/unbound-navigation.json` records this. The table does not support any claim.

## Searches

`private/search/*-paths.txt` are path-only ripgrep receipts over `frontier`, `experiments`, `iterations`, `proposals` and `scouts`, including hidden and ignored files of any size, with this round's root excluded. They cover three pattern sets: off-diagonal Ramsey (689 paths), hypercube Ramsey (845) and unit distance (1209). Most hits are metadata copies, catalogue copies, Lean build files and copied source bodies. I filtered them to authored `.md`/`.json` notes and opened the operative hits listed above. A hit is not a semantic read, and a missing hit is not evidence of absence. An earlier family-number search in the `frontier` notes guided the 166/176/164/160/159 history reads.

## Computation

No finite computations or numerical checks were run. The calculations in the public notes are by hand and are prefreeze feasibility work, not certified proofs.
