# Exact common-pin geometry and the polynomial-rank debt

This is an author-side derivation within the unchanged full pinned target, not a candidate proof or a general impossibility theorem. It treats d=3, which already must be solved for that target. The starting pair-flat coordinates are exactly source reduction.tex and motions.tex; the latter's null-form/two-family operation was read at lines285–375.

## 1. A single quadric contains the common-pin incidence construction

Write Zx=w×x, where w∈R³. For q≠r put v=(q+r)/2 and y=(q−r)/2≠0. The source affine3-flat is

    F_{q,r}={ (w,c): c=y−w×v }.

The diagonal flat for an actual pin p is

    D_p=F_{p,p}={ (w,c): c=−w×p=p×w }.

Let Q(w,c)=w·c. Every D_p lies in Q=0. On F_{q,r}, Q=w·y. Hence every common-pin intersection D_p∩F_{q,r} lies in the affine2-plane

    E_{q,r}={c=y−w×v, w·y=0},

which itself lies in Q=0. The condition for this intersection is

    w×(v−p)=y.

If p≠v, a solution exists precisely when y·(v−p)=0, equivalently |p−q|=|p−r|. For that case the solutions form an affine line in w-space, parallel to v−p, and yield an affine line in E_{q,r}. Distinct pins p≠v give distinct such lines: if their lines agree, the two vectors v−p and v−p' are parallel; writing v−p'=t(v−p) in the same nonzero equation forces t=1. No positivity or complex generic-position assertion is substituted for this elementary real calculation.

The midpoint p=v is an actual isosceles witness but has no finite intersection: the equation becomes0=y. At most N(N−1) ordered triples have p=(q+r)/2, and at most N(N−1) have q=r. Removing both from T costs O(N²), negligible compared with N³/M in the hypothesized M=o(N^{2/3}) regime. This exception must be removed, not implicitly declared impossible.

## 2. The construction is weighted bisector-plane incidence

Let H={x:y·(x−v)=0} be the perpendicular bisector plane of q,r. Its associated linear3-space is

    B_H={ (w,c): w·y=0, c=v×w+h y for some h∈R }.

It is contained in Q=0. Rescaling y or replacing v by another point of H gives the same B_H, since the cross product of two vectors in y-perp is parallel to y. The plane E_{q,r} is the h=1 affine slice for this chosen y,v.

These equations are ordinary line coordinates: for a line through p with direction w, its moment is c=p×w, so its coordinates belong to D_p. A line contained in H has w·y=0 and (p−v)×w parallel to y, so belongs to B_H. Conversely these moment equations describe the same lines. Projectivizing gives the two plane families on the split quadric of line coordinates. In particular D_p meets B_H in a2-dimensional vector space when p∈H; the h=1 slice loses just the midpoint case explained above.

Thus the proposed common-pin rigid-motion repair does not bypass the original incidence problem: it is weighted point–bisector-plane incidence in line coordinates. If multiple unordered pairs share the same bisector, the corresponding multiplicity must remain. With w(H)=#{unordered {q,r}⊂P with bisector H}, the nondegenerate isosceles count is exactly

    2 Σ_H w(H) |P∩H|,

before subtracting midpoint witnesses if one uses the affine motion patch. Dropping w(H), or treating all pairs as distinct projective planes B_H, loses the counting problem. Each w(H)≤N/2 because reflection in H pairs each off-plane point with at most one partner, but that upper bound alone does not supply the sharp total estimate.

## 3. Why the literal sampling-rank budget misses the target

Since Q is a nonzero quadratic polynomial in six variables, the space of restrictions of polynomials of total degree≤D to Q=0 has dimension

    H_Q(D)=binom(D+6,6)−binom(D+4,6)=Theta(D⁵).

The formula follows because Q is irreducible (its quadratic form has rank6, whereas a product of linear forms has rank≤2) and its ideal is the principal ideal(Q); multiplication by Q is injective and shifts degree by2. For D<2 the second binomial term is zero.

A polynomial restriction to one diagonal3-flat has dimension binom(D+3,3)=Theta(D³). The immediate source-style estimate for θN sampled diagonal flats therefore charges at most θN Theta(D³) conditions. It does not charge the surrounding full six-dimensional space Theta(D⁶), since all relevant flats are on Q. Comparing this raw charge with the ambient rank ceiling Theta(D⁵) places the scale at D of order sqrt(N). At a pair-plane E_{q,r}, a nonzero polynomial of degreeD can vanish on at mostD distinct affine lines: their distinct linear equations divide its restriction, and their product has degree equal to their number. The available average number of pin-lines per pair is of order N/M. It only dominates sqrt(N) when M=o(sqrt(N)), below the desired scale N^(2/3).

This is a limitation of the specified raw rank-budget argument. An upper bound on a sample's rank exceeding the ambient dimension does NOT prove its actual rank is large or that no useful polynomial exists. Dependencies, specially chosen samples, weighted decomposition, or another construction might change the argument. None is proved here. In particular the full frozen target is neither proved nor refuted by this calculation.

The finite diagnostic checks/motion_quadric_rank.py forms the actual integer restriction matrices for deterministic rational pins and reduces modulo the verified prime1000003. For degrees1,2,3,4 the ranks saturate H_Q(D)=7,27,77,182 after3,5,8,10 pins, respectively. Because reduction modulo a prime cannot increase integer-matrix rank over Q, and the quadric multiples already give the matching upper bound, these are exact ranks for those finite rational clouds. Their kernel through that degree consists exactly of quadric multiples, which vanish on every E_{q,r}. This is finite evidence for the stated rank issue only; no asymptotic claim or all-cloud statement is inferred.

## 4. Maximal-isotropic exception is not removed by pinning

In the source's global evaluation-flat parameterization, the diagonal pair parameters have [v:y]=[(p,1):0]. All of them lie in the single maximal isotropic projective plane y=0. If one tries to apply the source concentration theorem to the diagonal family at a smaller scale D, its explicit hypothesis requires N≤C D^(d−1). This fails at the tempting D=N^(1/d) scale, by a fixed power, for every fixed d. The original scale A=N^(2/d) had room for this cap; changing both the family and the scale is not a permissible formal substitution.

At an off-diagonal pair, all local common-pin parameters [u+w:u−w] similarly have a fixed second coordinate up to their common normalization and come from centers on one bisector. Their pairwise quadratic pairings vanish. Thus they occupy one maximal-isotropic exceptional family, geometrically the same reflection in that bisector. The source concentration exception is exactly active here. This does not disprove a new estimate for that special weighted family; it states the extra estimate that a successful repair still owes.
