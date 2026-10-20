# r132 reading limits

Author: Myeongjin Kang (no affiliation). CC BY 4.0.

- **Timing.** Briefs, AGENTS.md, r130/r131 records, FHLX §4, I43 §1.3 and r112 were read before any computation.
  Source P (pinned, authenticated) and the arXiv metadata/web check were read after the exploration runs and before
  the PREFREEZE decision. These are late reads. Neither changed the direction. Nothing was frozen, so no frozen bytes
  are involved.
- **Upstream.** Source P (`A-product-counterexample-...-September-24-2026`): all 4 tree blobs were fetched at the pin
  and authenticated against the complete 13223-entry tree (Git blob SHA-1 and size). Only `build/main.tex` lines
  38–237 were read (introduction, `thm:counterexample`, `lem:facets`, `prop:product`). README, references.tex and
  the PDF were acquired but not read. The Petty-minimum companion (source PM) was not read, because its theorem
  concerns the minimum, which is a different functional extremum.
- **Primary.** FHLX was read from the project-retained I43 text: lines 1–400 and 560–1092. The dimension-three
  equality section (lines 401–559) was not read, as it does not bear on §4. arXiv 2610.13953 was checked as metadata
  only (v1). Two bounded web queries were run. This is not priority clearance. Classical ingredients (Minkowski
  existence/uniqueness, Curry–Schoenberg, Gamma–Dirichlet independence, McMullen's cube-projection formula) are used
  as standard, and their primary bodies were not re-read.
- **History.** See private/registers/history-register.json for extents, queries, counts and exclusions. The active
  roots fresh-arithmetic-discovery-r98, t106o133-contribution-r1, t106o133-proof-r1 and fresh-structural-discovery-r134
  were neither read nor searched. The r131 root was read only and left untouched: no code was run there, and its
  environment was not copied.
- **Mathematics.** R1–R4 and (★) are author derivations written to sketch standard and checked numerically, but not
  independently reviewed. All tables are float or Monte Carlo exploration from scratch/ (pure Python, one process,
  `ulimit -v` 1 GB). None is a proof or a certificate. No upstream theorem was audited.
