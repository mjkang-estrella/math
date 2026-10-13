# I237 — cube cylinder bound: analytic record

Status: proof checked directly; final contribution verdict: technical corollary, do not count. 2026-10-12. The initial mathematical paragraphs were written before the literature screen.

Let C=[-1,1]^3. A cylinder is B+R u for a unit vector u and a Lebesgue-measurable B subset u-perp. Assume a finite family covers C. Infinite-area bases make the conclusion immediate.

For 1<R<=sqrt(2), define f_R(x)=1_C(x)1_{|x|<R}/sqrt(R^2-|x|^2), with value zero on |x|=R. On an affine line x=y+tu, y perpendicular to u, the unrestricted ball density has integral pi if |y|<R, and zero if |y|>=R. Indeed its nonzero interval is (-a,a), a=sqrt(R^2-|y|^2), and its integral is integral_{-a}^a (a^2-t^2)^(-1/2)dt=pi. Restriction to C can only decrease the integral. This handles tangent lines and boundary values explicitly.

The ball mass is pi^2 R^2, by integrating its line integrals over the radius-R disk. At fixed x_1=s, its two-dimensional section integral is 2pi sqrt(R^2-s^2), by polar integration. The six caps |x_j|>1 are disjoint inside the open ball for R<=sqrt(2): two such strict inequalities would imply |x|^2>2. Thus

    M(R)/pi = pi R^2-12 integral_1^R sqrt(R^2-s^2) ds
            = pi R^2-6R^2 arccos(1/R)+6sqrt(R^2-1).

Its derivative is 2R(pi-6arccos(1/R)), positive before R=2/sqrt(3) and negative after, in this interval. At R=2/sqrt(3), M(R)/pi=2sqrt(3).

Tonelli in the coordinates u-perp plus R u gives integral_{B+R u} f_R <= pi |B|. Nonnegativity and the cover give M(R)<=pi sum |B_i|. Therefore sum |B_i|>=2sqrt(3). The same proof works for a cover up to three-dimensional Lebesgue-null sets. The cube's projection area is 4(|u_1|+|u_2|+|u_3|), with minimum 4 over unit u, so the absolute bound divided by minimum projection is sqrt(3)/2. This is not a directionwise normalized bound.

There is no unpaid proof step in this inequality. Its proof uses the classical singular-ball line-integral certificate, truncation by a cube, disjoint caps, and one-variable calculus. No novelty or substantiality follows from these computations alone. R015's already accepted tetrahedral quadratic-envelope theorem is not re-proved or counted here.

## Exact theorem and scope

For every positive integer N, every choice of unit vectors u_1,...,u_N in R^3, and every choice of Lebesgue-measurable sets B_i subset u_i-perp, if C subset union_i(B_i+R u_i), then

    sum_i area(B_i) >= 2sqrt(3).

No boundedness, convexity, connectedness, regular boundary, or common direction is imposed on the bases. Infinite area makes the assertion immediate. A translation, rotation, and similarity of ratio a>0 gives 2sqrt(3)a^2 for a cube of side 2a, equivalently (sqrt(3)/2)s^2 for side s. Countable covers also satisfy the same estimate by Tonelli, although the requested theorem is finite. Weighted finite covers, with nonnegative weights and weighted multiplicity at least one almost everywhere on C, obey the corresponding weighted area inequality by the identical integration argument. These extensions are technical variants, not separate findings.

For completeness, the projection formula follows by projecting the faces visible from u. Each coordinate pair of faces contributes one face of area 4 times |u_j|; these projected faces cover the shadow with disjoint interiors almost everywhere. Hence A_C(u)=4 sum_j|u_j|, whose minimum is 4, attained at a coordinate direction. Thus sum area(B_i)/A_min(C)>=sqrt(3)/2. This expression has a single fixed denominator. It does not assert sum area(B_i)/A_C(u_i)>=sqrt(3)/2.

The line cap pi is attained at the chosen radius: the central body diagonal has ball endpoints (±2/3,±2/3,±2/3), and the whole ball chord lies in C. Thus no smaller all-line constant can be substituted for pi for this particular density. The radius maximization above is only for 1<=R<=sqrt(2). No optimum over all radii, centers, ellipsoids, or nonnegative densities is asserted.

## Benchmarks and the missing sharp result

The general 2009 directionwise bound gives the absolute lower bound 4/3 for C. The elementary volume/longest-chord bound gives 8/(2sqrt(3))=4/sqrt(3). The unit inscribed ball and Bezdek–Litvak's ellipsoid theorem give pi, the strongest of these benchmarks. The new elementary calculation improves pi to 2sqrt(3), with ratio 2sqrt(3)/pi>1. This comparison is a deduction from the old theorem, not a claim that pi was the published best cube constant.

Even maximizing the direct *inscribed-ellipsoid/minimum-projection* benchmark cannot improve pi. If E=c+A B_2^3 is contained in C and Q=AA^T, coordinate widths give Q_jj<=1. Its projection onto a coordinate plane has area pi sqrt(Q_jj Q_kk-Q_jk^2)<=pi. Hence A_min(E)<=pi; the inscribed unit ball attains pi. This does not rule out stronger consequences of other old results or a combination of certificates.

A single coordinate-axis cylinder with square base covers C at cost 4. This is an upper bound on the covering infimum, not a proof that every cover costs at least 4. The primary sources screened do not establish an arbitrary-axis cube lower bound of 4. Neither its truth nor its absence elsewhere is settled by this search. The rigorously justified interval here is [2sqrt(3),4].

## Actual connection to the stipulated upstream family

Write E(D,V,L)={(s,p+sV(p)):p in D, |s|<=L}, F_h(s,p)=(s,p_1,h p_2), and J_h(v)=(1+v_1^2+h^2 v_2^2)^(-1/2). Suppose D subset R^2 is compact, V is C^1 on an open neighborhood of D, L,h>0, tr DV=0, and -L^(-2)<det DV<=0 on D. If

    C subset F_h(E(D,V,L)),

then

    h integral_D J_h(V(p)) dp >= 2sqrt(3).

Proof: the pinned ruled-set companion's Theorem b:approximation, with Proposition b:projection, supplies for every eta>0 a finite cover of F_h(E) of physical cost at most h integral_D J_h(V)+eta. It also covers C. The cube theorem gives 2sqrt(3)<=h integral_D J_h(V)+eta; let eta decrease to zero. All field, length and physical-scale data are fixed before eta is chosen, just as in the source. This is a genuine implication using the accepted finite-realization operation. It is only an immediate obstruction to applying that operation to a cube at smaller cost, not a new finite-realization theorem.

The pinned angular, slope-field, and radial-sweep companions give tetrahedral upper covers and the same area model; their actual statements were read. They neither imply this cube lower bound directly nor enter its standalone density proof. Calling that proof repository-enabled would misstate its dependency. The above obstruction is the limited authentic connection, and does not rescue substantiality.

## Contribution decision and unpaid work

The cube inequality is correct. An exact prior publication of its constant was not located in the bounded primary screen. That is not worldwide novelty evidence. The proof's distinctive calculation is subtracting six disjoint spherical caps and optimizing one scalar; the singular density and all-line estimate are explicitly present in the 2009 source. In contrast, R015's accepted content is a sharp offset-sensitive quadratic envelope and its realizing chord family, not merely applying the integration principle. I237 is not literally a parameter substitution in R015, but it supplies no comparable new bridge.

Decision: **retain as an elementary technical corollary; do not nominate or count it as the tenth substantial finding.** No nearby general-box or unconditional-body theorem was pursued because no nonroutine bridge emerged. Remaining unpaid work would be either a substantially stronger theorem with a new argument, or primary evidence that this elementary cube estimate resolves a recognized substantive gap. An arbitrary-axis lower bound of 4 and optimality among all densities are unproved here.
