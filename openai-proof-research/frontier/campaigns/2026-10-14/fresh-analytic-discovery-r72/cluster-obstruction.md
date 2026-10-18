# One shell energy cannot generate several pressure corners

Author-level screening lemma, not a candidate theorem or contribution verdict.

Fix an integer M >= 2, p,c,a > 0 and e in R. Grant the favorable ideal bare pressure
q(beta,h) = max(0, max_{1<=m<=M} p[m h-c(m-1)-beta e m(m-1)/2]), beta>0.
Here p is the density of cluster centers, c is the entropic cost per added particle,
and e is a common energy per internal edge. This is an abstract model; no new
microscopic core realizing it is asserted. Source228 has M=4,c=3,e=0.

Apply the source operation T_a q = sup_u[q(beta,h+beta a u)-beta a u^2/2].
A finite maximum commutes with supremum. Completing the square for each branch,
including the vacuum, gives exactly P=max(0,B_1,...,B_M), where

B_m/p = c + m(h-c+beta e/2) + beta d m^2/2,  d=ap-e.

Claim: P has a subdifferential with nonempty interior in the (beta,h) plane
at exactly one point if d>0, and at no point if d<=0. In particular this family
cannot generate two temperature corners of the source's preserved-ball type.
This says nothing about other microscopic models, actual finite-t rounding,
or singularities not witnessed by such a two-dimensional subdifferential.

Proof for d>0. Strict convexity in the integer m implies that only m=1,M
can maximize among the nonvacuum branches. Thus three noncollinear active
slopes require precisely B_1=B_M=0. The first equality gives h=-beta ap/2.
At this h, B_m/p=(m-1)(-c+beta d m/2). Consequently the unique solution is
beta=2c/(Md), h=-cap/(Md). Intermediate branches are strictly negative.
The determinant of gradients of B_1 and B_M is
-p^2 d M(M-1)/2, which is nonzero. Their convex hull with the vacuum gradient
therefore has interior. Elsewhere there are at most two active slopes.

Proof for d=0. Write L=h-c+beta e/2. All nonvacuum branches are c+mL.
If L differs from zero, only an endpoint maximizes. If L=0, all equal c>0,
so the vacuum is inactive. Their gradients p m(e/2,1) are collinear.
The subdifferential always has empty interior, including vacuum ties.

Proof for d<0. Strict concavity in m implies at most two integer maximizers,
and any pair is adjacent. At a tie of m and m+1, L=-beta d(2m+1)/2,
and the common value divided by p is c-beta d m(m+1)/2>0. Hence the vacuum
is not active at such a tie. At any vacuum tie there is at most one active
nonvacuum branch. Again the convex hull of active gradients has empty interior.
This proves the claim for every parameter, not just sampled values.

The finite-maximum subdifferential identity used here follows directly:
active gradients give global supporting planes; if a proposed subgradient lies
outside their convex hull, separation supplies a direction in which its slope
exceeds every active slope. Inactive planes have a positive finite gap and
remain inactive for sufficiently short motion, contradicting support.

Interpretation. Intermediate cluster sizes in the unmodified source already
lie below the endpoint envelope. A single edge penalty can make neighboring
sizes active, but their crossing is above the vacuum and supplies only a line
segment of slopes. To obtain several preserved support balls, one needs a
nonquadratic cluster energy/entropy envelope or another genuine operation.
Multiple radial shells might provide that, but their mixed-cluster geometries,
root-packing density, entropy exponents and complete upper pressure bound
have not been established here. Simply assigning desired energies to abstract
labels is not a radial pair-potential construction.
