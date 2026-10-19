# Reading, provenance, timing and failure limits (contribution review r1)

Reviewer: Factory Droid (Fable 5.1), T3-owned delegated task twenty-20261019-t372l127-contribution-factory-r1. Started 2026-10-19 after the parent dispatch at 13:35:25 UTC. No nested agents. No git operations. No edits outside frontier/campaigns/2026-10-14/t372l127-contribution-r1/.

## Not opened (as instructed)
discovery-analytic-r127-parent/proof-review-brief.txt; frontier/campaigns/2026-10-14/t372l127-proof-r1/. The proof-review-dispatch.json filename was seen in a directory listing only.

## Author packet (fresh-analytic-discovery-r127), read in full
REPORT.md, FINAL.json, packet/public/{frozen-scope.md, freeze.json, proof.md (Sections 1-9), transport-calculation.md, boundary-calculation.md, consistency-check.md, prefreeze.md, other-screens.md, reading-limits.md, report.md}. SHA256 of all of these recomputed; the six detached anchors in the brief (FINAL, REPORT, MANIFEST, frozen scope, proof.md, controls receipt) all match. Private metadata inspected: upstream/372-paths.json, primary/register*.json, history/register.json (head), work/prepare.py; the private upstream register.json was loaded but its 372 entries were not individually printed. packet/public/verify.py and controls/run_controls.py were NOT executed by this reviewer (the parent already replayed them); their code was not needed for this contribution review.

## Stipulated source372, read in full
All six retained sections of preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026 (introduction, boundary-reduction, analytic-estimates, physical-amplitudes, transport-matching, coefficient-recovery), from the author's retained canonical copies (SHA256 recorded in FINAL.json). Not freshly re-fetched from the pinned raw URLs; the author's register records blob checks against the complete 13223-entry tree, and the parent verifier replay accepted them. Labels cited: thm:main, lem:common-extension, prop:physical-transfer, lem:augmented-system, prop:carleman, cor:physical-solvability, lem:scaled-interior, lem:planar-frames, prop:physical-amplitudes, lem:transport-normal-form, lem:supported-transport, prop:transport-matching, lem:conic-bundle, prop:comparison-rigidity, lem:finite-type.

## External primaries
Retained author copies: Ruland-Salo 1708.06307v1 (Prop 6.1 statement, lines 486-505, read; rest grepped); Lin-Nakamura 1708.00591v1 (abstract and introduction lines 1-120 read; whole text grepped for stability terms: none); Cekic 2309.09348v3 (Theorem 1.1 statement and surrounding context lines 60-110 read; grepped); Tan-Liu 2211.06650v1 (grepped only). Newly downloaded by this reviewer into private/downloads (HTML + text extraction, SHA256 in private/register.json): Diao-Durdiev arXiv:2610.14741v1 (abstract, contents, Sections 1.1-1.2 read; whole text grepped), Eberle-Harrach arXiv:1906.02194 (introduction paragraph via grep), arXiv:2505.05116 (introduction via grep), Carstea arXiv:2605.06354v1 (abstract and introduction via grep). Landing pages fetched (abstract only): Eskin-Ralston IP 18 (2002); Akamatsu-Nakamura-Steinberg IP 7 (1991); Kang-Yun SIAM J. Math. Anal. 34 (2002). Not read: NU 1994/2003, IY 2015, BFV 2014, BFMRV 2014, Alessandrini 1988, Sylvester-Uhlmann 1988 bodies.

## Project history
frontier/iterations/i112 (lines 1-60 read in full; remainder via grep hits), i115/i118/i121 (grep hits for stability/log/Lin-Nakamura/Eskin/Ruland/Cekic only). frontier/findings/R013 head read for calibration of the project's SUBSTANTIAL standard (it is a quantitative stability finding in convex geometry, unrelated to elasticity). frontier/reviews/i51, i278, i256 contribution verdict lines read for calibration. Project-wide rg for "T372", "logarithmic stab", "Imanuvilov" over authored markdown (excluding private copies): no prior T372 stability item.

## Searches
Eight WebSearch queries listed in literature-comparison.md; receipts in public/search-receipts.json. Searches are lexical navigation, not semantic reads or priority clearance.

## Failures and tool limits
One ripgrep pattern with a bracketed accented character returned nothing (regex handling); replaced by plain queries. Large grep outputs were truncated by the terminal; all needed hits were recovered in bounded follow-ups. No download failed. No numerical experiment was run. No mathematical counterexample is asserted.

## Timing
All reading by this reviewer postdates the author's freeze (2026-10-19 12:34 UTC) and the parent authentication (13:35 UTC). Nothing here can be backdated.
