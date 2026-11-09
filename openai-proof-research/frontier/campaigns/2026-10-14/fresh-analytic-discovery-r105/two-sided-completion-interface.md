# Exact two-sided completion criterion for one lattice

This is paid Erdős--Rogers convex completion adapted to the source's torus multiplication lower bound. It is a supporting reduction, not a new analytic estimate or nomination. The original1962 primary was downloaded and all244 extracted lines read, including its final high-multiplicity argument.

Let K be a convex body, Gamma a full-rank lattice, k>=3 integer, eta=1/k, and H a positive integer. On the Gamma torus put

 delta0 = measure of points NOT in (1-2eta)K+Gamma;
 deltaH = measure of points with at least H translates of K.

If both delta0 and deltaH are strictly below k^(-n)(1-delta0), then (1-eta)K+Gamma covers EVERY point with multiplicity strictly below H.

Indeed pi(K) has measure at least1-delta0: a translate of (1-2eta)K is contained in K by convexity. Multiplication by k sends pi(eta K) onto pi(K), so pi(eta K) has measure at least k^(-n)(1-delta0). If x is not covered by the middle body, x-pi(eta K) is contained in the inner body's holes, since (1-2eta)K+eta K=(1-eta)K. This contradicts the measure bound. If x is covered by at least H DISTINCT middle translates, every point of x+eta K is covered by those H outer translates, so x+pi(eta K) lies in the outer high-multiplicity set, again a contradiction. No packing assumption and no symmetry or origin assumption is needed.

Rescaling Gamma by (1-eta)^(-1) makes this an exact cover of K with the same maximum multiplicity. Thus the full target would follow from one lattice of mean outer density O(nlog n) simultaneously satisfying delta0,deltaH<exp(-nlog n-O(n)) at eta~1/n and H=O(nlog n).

The source supplies a small-hole selection mechanism but no corresponding upper-tail mechanism. The classical Erdős--Rogers independent-coset binomial calculation supplies both tails for a PERIODIC UNION OF COSETS, not a single lattice. Replacing independent centers by all points of their generated subgroup changes both the law and multiplicity; that is not permitted here.

This clarifies the earlier cube counterexample: a small-hole assumption alone cannot preserve peak. There is no obstruction to a two-sided completion once an OUTER high-tail bound is also supplied. The unpaid estimate is the simultaneous single-lattice outer tail, at the superexponentially small threshold written above, or a different exact-coverage mechanism avoiding that threshold.
