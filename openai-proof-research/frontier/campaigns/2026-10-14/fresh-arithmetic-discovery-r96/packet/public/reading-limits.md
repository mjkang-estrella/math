# Reading and timing limits

## Timing

- No freeze happened at any point.
- Order of work:
  1. AGENTS.md and the full r96 brief, including the inherited text.
  2. The r95 handoff: outside `REPORT.md`, public `report.md`, `route-041.md`, `screens.md` (the brief calls it other-screens), `reading-limits.md`, and the parent `intake.json`.
  3. The family-history table, then targeted history searches.
  4. Source bodies.
- 001 and 028 were selected after the history searches. The 028 decision followed the geometry/preliminaries/periodicity reads and the targeted checks of the later sections.
- 013 and the 207 characteristic-$p$ idea were screened after the 028 analysis began. The I204, r72, r79 and r92 history bodies were read before any decision on the corresponding family.
- One error was corrected before sealing. The first draft of `route-028.md` claimed that $(E-E)-(E-E)$ contains the whole cube $[-m,m]^3$ and stated a Minkowski consequence for every sublattice. A finite enumeration at $m=6$ found that the two open octants $(-,+,-)$ and $(+,-,+)$ are missing (exactly $432=2\cdot6^3$ points). The text now states the correct set and limits the conclusion to volume/union-bound exclusion routes. A second finite check confirmed, over $\mathbb F_7$ with $a=(1,3,2)$, that cross products of vectors in $a^\perp$ lie in $\mathbb F_7a$ and can be nonzero. Both checks were one-off `python3 -c` runs that wrote no files. They are sanity checks, not proofs.

## Pinned source bodies

Every retained body was blob-checked against `sources/preprints-tree.json` (see `source-register.json`).

- **028 Bounded-Step Walks on Gaussian Primes:**
  - `main.tex`, `preliminaries.tex`, `geometry.tex` and `periodicity.tex` were read in full.
  - `coverage-transfer.tex`: lines 1–12 were read, plus `rg` for planar or Gaussian inputs.
  - `schedule.tex`: lines 240–265 were read, plus `rg`.
  - `information.tex`: lines 250–275 were read, plus `rg`.
  - The remaining lines of those three files were not read line by line.
  - `README.md` and `references.tex` were fetched, not read, and removed (hashes in the register).
- **001 Milne rationality:** `00_intro.tex` was read in full. `README.md`, `main.tex` and `05_reduction.tex` were fetched, not read, and removed. Sections 01–04 were not fetched.
- **013 additive indecomposability:** `01-introduction.tex` and `09-conclusion.tex` were read in full. `README.md` and `paper.tex` were fetched, not read, and removed. Sections 02–08 were not fetched.

## History copies

Eleven files were copied unchanged into `private/history/` (origins in `context-register.json`):

- the r95 handoff files;
- the r95 family-history table;
- I204;
- the r92 067 screen;
- r72 `screening.md`;
- r79 `public/research.md`.

r79 was read through its 207 sections (lines 1–90 and the summary near line 124). The other copies were read in full.

## Not acquired

No primary literature was acquired and no web search was run. These items are navigation only; `external-navigation.json` records which are cited in the pinned source text and which are runner background knowledge:

- Vardi; Gethner–Stark; Gethner–Wagon–Wick (cited in the 028 source);
- Kuga–Satake and Madapusi Pera integral models (001);
- Elsholtz–Harper and Green–Harper (013);
- the "rational Hodge conjecture for products of K3 surfaces" companion body, known from catalogue and path listing only.

## Searches

History searches used `rg -l` over authored directories with fixed phrases (Nagata/Seshadri, Margulis–Platonov, Milne rationality, Iitaka subadditivity, Campana–Peternell, klt complement, Shafarevich, fourfold termination, cubic fourfold, Gaussian moat, Ostmann). There was no size cutoff, but only the directories named in the commands were searched. Hits are navigation, not semantic reads or absence certificates. Copies of `preprints-tree.json` and catalogue snapshots inside other rounds were treated as navigation.

## Scratch

Nothing was written outside the owned root. The control script creates and removes `control-work/` inside the owned root. Harness-truncated command outputs were written by the tool harness outside the repository, not by this runner.
