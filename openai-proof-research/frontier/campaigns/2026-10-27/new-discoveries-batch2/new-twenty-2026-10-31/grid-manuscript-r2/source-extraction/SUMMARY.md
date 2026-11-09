# MathDB 343536 — Round 6 implementation

The Lean mathematical targets are closed: Grid343536.ordinary_border_transitivity :
OrdinaryBorderTransitivity, Grid343536.main_orbit_proved : MainOrbit, and the
UNCONDITIONAL GridFinal6.mathdb_343536. Root decides acceptance; no self-acceptance
or discovery credit is claimed.

New mathematical modules: GridColorFlags, GridColorTiming, GridCornerColors,
GridSideAlignment, GridInternalFlags, GridBorderFrames, GridOrdinaryBorder,
and GridFinal6. Audit6 supplies the full declaration audit.

Related corners are handled by reflection frames. Neighbour matching chooses
one of the two oriented flags. Side colour propagation and first-corner timing
rule out a direction swap in nonsquares; in squares, transposition realizes it.
An oriented matching flag determines the first row and then the full partition.

For internal border vertices, align a side chart or its reversal using the
saturated border rule. Backward non-backtracking propagation reaches a corner
at the same time, hence the positions agree. The resulting corner flags force
the entire side lengths to agree. The aligned chart therefore gives an actual
A0 map; row determinism makes it colour-preserving. Reflection and transpose
conjugation return witnesses to the original coordinates.

All 38 inherited round-5 modules are byte-identical. The bound round-5 archive
SHA-256 is 2ea9a4d731a026da9f564eb05f11254144b4874cae7fba57ba678ca23cfddd46.
All three target theorems print only propext, Classical.choice and Quot.sound.
Validation status is recorded in results.json and verification/replay-report.json.
