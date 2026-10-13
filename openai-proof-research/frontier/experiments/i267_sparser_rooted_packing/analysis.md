# I267 derivation and checks

The complete proposed proof is in frontier/iterations/i267-sparser-rooted-packing-transfer.md. No independent proof gate or acceptance is claimed.

Two replacements are both necessary. Self-bounding concentration replaces a relative-tail exponent of order mu²/n by order mu. A permutation martingale of length dq, instead of N, replaces the avoidance-tail exponent q²/N by order q. Improving only the first would leave the old sprinkling obstruction at low supply.

The deletion surrogate Z_v is defined by forbidding v in all candidate blocks, not by resampling only X_v or removing root labels. It is independent of X_v even though some other coordinate blocks store edges incident to v, since every such edge is ignored by the restricted optimization. Fixing one optimum proves the summed influence bound. There is no claim of independence of compatible d-block indicators.

With delta=n^(-1/3)(log n)², minimum mu is n delta/(4d). Compressed family size is O_d(delta^-1), so its logarithmic cost is O_d(n^(1/3)); the root-set cost is O(n^(2/3)log n). Both concentration stages dominate this cost by n^(2/3)(log n)². All cutoffs may depend on fixed d; the bound is uniform in permitted r,s.

Empty pattern families, edge-free patterns, repeated neighborhoods, and the two floor/cap cases are inherited with their explicit treatments in I257. No constraint on nonroot candidate lists is added; such a constraint could destroy permutation invariance. The result changes only the density range of the same rooted-packing chain, not the accepted count.
