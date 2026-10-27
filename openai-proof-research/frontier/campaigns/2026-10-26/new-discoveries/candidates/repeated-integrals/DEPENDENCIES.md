# Pinned mathematical dependencies

Lean4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52); mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612 and the8 dependency revisions in
verification/pins.json. The replay verifies revisions and tracked-file cleanliness.

Substantive library ingredients include Stieltjes measures and their atom/mass
formulas, within-derivative Taylor remainder, Fubini for interval integrals,
finite polynomial root sets, positive-definite matrix invertibility, smooth
bump functions, and finite-dimensional separation. In particular the separation
used here is mathlib's `geometric_hahn_banach_open_point`, at
Mathlib/Analysis/LocallyConvex/Separation.lean:125 in the pinned revision;
it is not an assumed lane theorem. See MomentRepresentation.lean and the
actual declaration types in verification/parent-Checks.log.

The source question is Burke–Haris–Madhavendra2512.02151v1 Conjecture1.2.
Known n≤3 cases and their conditional sequel2512.23949v1 are credited.
di Dio2411.03145v2 Theorem2.5/Corollary2.7 (published Corollary3.1,
DOI10.1007/s00013-025-02175-1) and its2019 predecessor are methodological
prior work, not new machinery claimed here. The proof is self-contained
relative to the pinned library and uses no source-paper theorem as a new axiom.
