# CHOICE — r2 family selection

**Chosen family: 113 — "Approximate counting and entropy of perfect matchings."**

## Why this family
- Finite combinatorial object (perfect-matching polytope; counting/entropy of perfect
  matchings), matching the campaign's preference for concrete finite estimates.
- Its entropy paper *explicitly flags* an unpaid finite estimate: the optimal coefficient
  $c^\*\in[\tfrac{\ln3}{2\ln(3/2)}\approx1.3548,\,2]$, stating that optimality of the
  coefficient two is *not* established. A named, flagged, unpaid constant.

## Freshness (bounded evidence, not a certification)
Screened by the campaign's standard bounded procedure:
- No `tasks.json` claim on family 113.
- Absent from the accepted-results audit.
- Only a catalogue entry and an unrelated K₆ / Metropolis mention appear elsewhere.
This is a **bounded** screen (registry + targeted semantic grep + accepted audit), consistent
with the campaign's standing caveat that freshness is never certified (cf. the earlier
silent-occupancy lessons for families 160 and 104). No collision with any active reservation
(101/161/187/206/224/298) or exclusion (012/031/144/290/292/322/338); family 186 is reserved
for the corrected archive only.

## Sources read (blob-verified fetch against the canonical tree)
- FPRAS paper `main.tex` (randomized approximation scheme for perfect matchings in general
  graphs; constants are algorithmic/technical, not a clean unpaid finite estimate).
- Entropy-and-Face-Dimension paper: `01-introduction`, `02-polytope`, `03-entropy`,
  `10-examples` (the main theorem, the sharp codimension bound $3m-2$, the trace obstruction,
  and the Klee/triangle-expansion lower-bound family).

## Reading limits
- The FPRAS paper was read for its main theorem and constants; its long algorithmic analysis
  was not exhaustively audited (it does not bear on the entropy coefficient).
- The entropy paper's structural sections (02, 03, 10) were read in full; remaining sections
  (e.g. detailed FPRAS-entropy corollaries) were not all read line-by-line.
- All freshness and gadget-nonexistence statements are bounded/computational as noted in
  candidate.md; numerical evidence is labeled as such and is not presented as proof.
