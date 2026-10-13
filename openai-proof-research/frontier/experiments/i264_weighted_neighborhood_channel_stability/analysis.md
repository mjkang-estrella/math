# I264 derivation map

The complete proposed proof is in `frontier/iterations/i264-weighted-neighborhood-channel-stability.md`. This is an unreviewed strengthening of one existing spectral nomination, not a new accepted finding.

The exact difficulty with removing essential-supremum control is that the first-channel coupling Q(w|f|² phi) need not be a fourth-order term relative to J. A pointwise Taylor expansion from I262 is insufficient. I264 instead retains both Feshbach coupling components and controls the first by a dual Sobolev estimate: B1<=K J integral w|f|²<=K C1 J^(3/2). The transverse coupling uses g=sqrt(1-|f|²)f and exact principal-channel centering. The favorable difference J-integral w rho|g|² supplies the large-angle contribution.

All operator perturbations are bounded in form norm relative to the compressed H0+a², through integral ||U||<=C1 sqrt(J). This is dimension independent and proves spectral isolation directly without analytic continuation. The threshold tail is controlled by the known operator-valued endpoint theorem followed by two weighted Holder inequalities. The second gives integral sqrt(w)|f|²<=Ctheta J^theta; it replaces the essential-supremum factor.

The constants are specified in the full proof. Their finiteness uses r>1, so no endpoint extension is claimed. The upper bound follows from the ground-state test, while the lower bound requires the compressed spectral comparison and the full threshold-moment tail. The conclusion assumes J small; no inference from D small to J small is made.
