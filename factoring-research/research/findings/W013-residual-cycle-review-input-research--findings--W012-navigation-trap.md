# W012 factor-selective navigation: an exact false basin

2026-10-08. Parent exact counterexample for a specified navigation rule,
not a factoring-performance experiment or a general navigation lower bound.

After the convex-cap coverage limitation, a different attempted computation
was to avoid full coverage: start near the balanced point of the integer
hull above xy=N, and follow adjacent vertices only when their product xy
does not increase. Reaching product N would factor. A related update uses
the returned vertex's own gradient slope y/x for the next support query.

The single preselected [certificate brief](W012-navigation-certificate-brief.md)
fixed N=21311=101*211 and v=(144,148), with v_x*v_y=21312=N+1.
The retained [exact hull](W012-navigation-certificate.json) was generated
by one finite certificate computation, not a search over N. Its initial
strict-local-minimum flag is FALSE because one neighbor has equal product.
The same retained data establish a stronger relevant fact for the proposed
non-increasing rule: the equal-product plateau is closed.

The consecutive hull vertices are

    (135,158), (144,148), (148,144), (158,135),
    products: 21330, 21312, 21312, 21330.                 (1)

Both middle vertices are nonfactors. A move allowing equality can only
switch between them; reaching either outside neighbor increases product.
Thus neither strict descent nor non-increasing adjacent descent can escape
this plateau to the actual factor vertices. No replacement instance or
second enumeration was used.

## Small independent support certificate

The adjacency statements do not have to rely on trusting a full scan.
For all positive real points above xy=N, AM-GM implies
(a*x+b*y)^2>=4abN. The objectives are integers at lattice points.

For x+y the least possible integer objective is 292, since
291^2 < 4N=85244 < 292^2. The feasible points on x+y=292 have
integer x=144,...,148, from x^2-292x+21311<=0.
Only (144,148) and (148,144) are its exposed edge endpoints.

For 10x+9y, the continuous lower bound puts the integer minimum at
least 2770. On a fixed objective s, x must satisfy x=s mod 9 and

    x*y = x*(s-10x)/9.

This is a concave quadratic centered at s/20. At s=2770, the two nearest
allowed x values are 133 and 142, whose products are 21280 and 21300.
At s=2771 they are 134 and 143, with products 21306 and 21307.
All are below N; concavity excludes every other allowed x at those levels.
At s=2772 the only feasible allowed x values are 135 and 144, with the
products in (1). The next allowed values 126 and 153 already give
21168 and 21114, and all farther values give smaller products.
So the exposed edge at minimum 2772 has exactly these two endpoints.
Reflection in x=y proves the other outer edge. This proves (1).

The gradient update at (144,148) uses slope 148/144=37/36.
Its integer objective is 37x+36y, and

    37x+36y = (10x+9y)+27*(x+y) >=2772+27*292=10656.

Equality in both supporting inequalities uniquely gives (144,148).
Thus the next support optimizer is the same nonfactor vertex: an exact
false fixed point. Reflection gives the same fact on the other half.

## Cost and constructive consequence

The proposed savings were factor-selective navigation with a small
number of already-priced support/neighbor queries. This example refutes
its claimed global descent mechanism. It does not refute algorithms
which cross barriers, choose distant slopes, batch vertices, use modular
arithmetic, or gain information beyond the product value.

A changed navigation method must specify and price how it crosses or
skips such nonfactor basins. The missing step is not convex optimization
itself. Searching more initial tangents without a success/query bound
would be a new unpriced restart assumption. No such repair or numerical
run is selected here.

Reproduction of the exact finite hull certificate: for x=1,...,N append
(x,ceil(N/x)) in increasing x order, repeatedly removing the preceding
point when the cross product of the last two edge vectors is <=0.
This standard lower-chain computation retains no collinear interior
points. It yielded 136 vertices, all preserved in the JSON. This
enumeration costs O(N) here and is not the proposed fast hull primitive.
The explicit supporting inequalities above are the mathematical
counterexample; the finite list supplies a reproducible cross-check.
