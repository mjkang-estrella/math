# I211 independent tetrahedral lower-bound proof review

2026-10-12. **PASS**, for the lower-bound theorem and the precise quadratic-certificate optimization stated below. No mathematical correction to I209 Sections 2–5 is required. This is an independent proof gate, not a contribution or count decision. All pinned source theorems and lower operations are stipulated true. I203 and the failed upper-cover route are unnecessary for this verdict.

For every regular tetrahedron T of edge length e>0, every positive integer N, every choice of unit directions u_i, and every family of Lebesgue-measurable bases B_i contained in u_i-perp with finite planar area,

    T subset union_(i=1)^N (B_i + R u_i)
      implies sum_i |B_i| >= (sqrt(15)/9) A_min(T)
                               = e^2 sqrt(30)/36.

For the same T, among all nonzero real polynomials q of degree at most two with q>=0 on T, the supremum of

    integral_T q dx / (A_min(T) sup_affine_lines ell integral_(ell intersect T) q ds)

is exactly sqrt(15)/9. Here polynomial describes q on T, and the ambient density is q 1_T; no global nonnegativity of the polynomial outside T is required. This asserts optimality of this single-uniform-line-bound certificate class, not optimality of actual covers, arbitrary densities, or directionwise normalized covering cost.

## 1. Regular tetrahedron and minimum shadow

Use vertices (1,1,1)/sqrt(2), (1,-1,-1)/sqrt(2), (-1,1,-1)/sqrt(2), (-1,-1,1)/sqrt(2). They sum to zero, have squared norms 3/2, pairwise inner products -1/2, and pairwise distances 2. Thus for sum lambda_i=1,

    |sum lambda_i v_i|^2 = 2 sum lambda_i^2 - 1/2.

The physical model with vertices (+-1,0,0),(0,+-1,sqrt(2)) is congruent after centering; integrating its sections gives volume 2sqrt(2)/3. Its diameter is 2: for convex combinations p,q, write p-q=sum_ij r_i s_j(v_i-v_j) and use the triangle inequality.

Independently verify the minimum rather than identify it with an unproved visual shadow. For a unit direction u let d_i=D_u lambda_i and s=sum_(d_i>0) d_i. The entering-facet formula gives A(u)=3 volume(T) s; zero derivatives contribute zero, so directions parallel to faces are included. Since sum d_i=0 and u=sum d_i v_i, positive and negative parts express u=s(p-q) with p,q in T. Hence 1<=2s. In direction (v_i-v_j)/2, the derivatives are +1/2,-1/2,0,0, so equality occurs. Therefore A_min=sqrt(2).

This agrees with the actual retained statements c:normal-frame and c:nil-projection in slope-projection.tex, and prop:simplex and eq:regular-normalization in radial-projections.tex. A second independent check uses the outward unit normals: sum n_i=0 and sum n_i n_i^T=(4/3)I. If P=sum (u.n_i)_+, then 4/3<=2P^2 and A(u)=sqrt(3)P>=sqrt(2), with equality in an edge direction.

The barycentric marginal is 3(1-t)^2 dt, since the sub-tetrahedron lambda_i>=t has relative volume (1-t)^3. Thus mean lambda_i^2=1/10, and mean |x|^2=3/10. No center or metric factor is missing.

## 2. Every chord, including short and boundary chords

Put f_a=(a-|x|^2)1_T for a>=3/2. This is a nonnegative bounded Borel density because |x|^2<=3/2 throughout T. If a line meets T in a segment with midpoint m, length l, and unit direction u, integrate x=m+tu for -l/2<=t<=l/2. The odd cross term integrates to zero even when m.u is nonzero. The exact integral is

    l(a-|m|^2-l^2/12).

For barycentric endpoint vectors r,s, write w=(r+s)/2. The identities give l^2=2 sum(r_i-s_i)^2 and |m|^2=2 sum w_i^2-1/2. More precisely,

    |m|^2 - (l^2/4-1/2) = 2 sum r_i s_i >=0.

The only endpoint hypothesis used is r_i,s_i>=0. Equality holds exactly when their supports are disjoint. Combining this with |m|^2>=0 and l<=2 yields the two upper envelopes

    F_1(l)=l(a-l^2/12),           0<=l<=sqrt(2),
    F_2(l)=l(a+1/2-l^2/3),       sqrt(2)<=l<=2.

They agree at sqrt(2). On the first interval F_1'=a-l^2/4>=a-1/2>0; short chords therefore cannot exceed F_2(sqrt(2)). On the second interval F_2'=a+1/2-l^2. For 3/2<=a<=7/2 the maximum is at sqrt(a+1/2); for a>=7/2 it is at 2. Both transition endpoints are covered. The envelopes need not be attainable at every short length; this is not used.

For attainability choose r=(z,1-z,0,0), s=(0,0,z,1-z), 1/2<=z<=1. Their supports are disjoint and l^2=2+8(z-1/2)^2 fills [2,4]. They give full line intersections with T: extending beyond r or beyond s makes at least one barycentric coordinate negative, also at z=1/2 and z=1. At z=1 the chord is an edge, a legitimate boundary line. Thus the upper bound is attained for every a in the asserted range, giving exactly

    M(a)=(2/3)(a+1/2)^(3/2),     3/2<=a<=7/2,
    M(a)=2(a-5/6),               a>=7/2.

Empty intersections and singleton tangencies have one-dimensional integral zero. Other lines in a face or along an edge obey the same barycentric argument. In particular there is no missing exceptional direction or offset.

At a=19/10, z=(1+1/sqrt(5))/2 gives l^2=12/5. Direct substitution gives

    mass = (2sqrt(2)/3)(19/10-3/10)=16sqrt(2)/15,
    M = (2/3)(12/5)^(3/2)=16sqrt(15)/25.

Their ratio is sqrt(30)/9; division by A_min=sqrt(2) gives sqrt(15)/9.

## 3. Arbitrary measurable bases and finite covers

For each u, the map (b,t)->b+tu from u-perp times R is an orthogonal coordinate map with Jacobian one. A Lebesgue-measurable B gives a Lebesgue-measurable cylinder. One explicit way to handle completion issues is to choose a Borel B_0 differing from B inside a planar null set N. On every bounded axial interval, N times that interval is a three-dimensional null set; the full cylinder difference is a countable union of these. Thus use of completed Lebesgue measure causes no gap.

The function f_a is Borel and nonnegative. Its line integral h_u(b)=integral_R f_a(b+tu)dt is measurable, and is <=M(a) for every b, not merely almost every b. Tonelli consequently gives

    integral_(B+R u) f_a dx = integral_B h_u(b)db <= M(a)|B|.

For a finite cover, 1_T<=sum_i 1_(B_i+R u_i) pointwise. Multiply by f_a and integrate. The resulting mass inequality proves the theorem above. Bases may be unbounded, disconnected, nonconvex, or modified on null sets. Translation of a cylinder is absorbed into its perpendicular base. A null base has zero f_a-mass and cannot evade the inequality. Infinite base area makes the claimed inequality trivial if that extension is desired. No compactness or existence of an optimal cover is used.

Coverage of the entire closed T is more than the proof needs: coverage up to three-dimensional null sets suffices. Boundary line integrals are included in M, so no boundary convention is silently used to lower it. Scaling by e/2 multiplies all base areas and A_min by e^2/4, proving the stated formula for every positive edge length.

## 4. Optimization over all, including nonsymmetric, quadratics

For an admissible nonzero q, its mass is strictly positive. Otherwise continuity and nonnegativity would make it vanish throughout the interior of T, forcing the polynomial to vanish identically. Its maximum line integral is finite, bounded by 2 max_T q, and positive because q is positive in some interior ball.

For the finite orthogonal tetrahedral symmetry group G define q_bar(x)=|G|^-1 sum_g q(gx). Changing variables shows equal mass. Each g preserves T, nonnegativity, degree, and arclength; for every affine line ell,

    integral_(ell intersect T) q_bar
       = average_g integral_(g ell intersect T) q <= M(q).

Hence M(q_bar)<=M(q), q_bar is nonzero, and Cert(q)<=Cert(q_bar). This is the required direction of the inequality. It proves that searching radial quadratics bounds every nonsymmetric competitor, without claiming that nonsymmetric maximizers cannot exist.

In the displayed vertex coordinates, the group contains every coordinate permutation and every sign change of two coordinates. The latter kill every linear and mixed quadratic monomial in an invariant polynomial; the former equate the diagonal coefficients. Thus q_bar=alpha+beta|x|^2.

If beta>=0, positivity at 0 implies alpha>=0, and alpha,beta are not both zero. An edge has length 2 and mean squared norm 5/6. Its integral gives

    Cert(q_bar) <= (alpha+(3/10)beta)/(3alpha+(5/2)beta) <= 1/3.

For the last comparison, multiply by the positive denominator: 3alpha+(9/10)beta<=3alpha+(5/2)beta. Constants and beta=0 are included; the estimate need not be sharp for beta>0.

If beta<0, positive rescaling reduces to a-|x|^2. Nonnegativity is equivalent to a>=3/2, since the vertices attain the maximum radius and all of T lies inside that sphere. The exact preceding mass and line maximum give

    R_1(a)=(a-3/10)/(a+1/2)^(3/2),    3/2<=a<=7/2,
    R_2(a)=(a-3/10)/(3a-5/2),        a>=7/2.

Here

    R_1'(a)=(19/20-a/2)/(a+1/2)^(5/2),
    R_2'(a)=(-8/5)/(3a-5/2)^2.

The formulas match at 7/2. R_1 increases up to 19/10 and decreases thereafter; R_2 strictly decreases. The unique radial maximum is therefore at 19/10 and equals sqrt(15)/9>1/3. The admissible q=19/10-|x|^2 attains it, completing both directions of the global optimization proof. Even interpreting polynomial nonnegativity almost everywhere on T would give the same class, by continuity.

## 5. Counterexample search, dependency limits, and the upper route

The written checks deliberately addressed edge-aligned and face-contained lines, singleton tangencies, short chords where the raw midpoint lower bound is negative, both breakpoints a=3/2 and 7/2, zero or unbounded measurable bases, the zero-polynomial exclusion, beta=0, positive beta, and arbitrary linear/mixed terms before symmetrization. None defeats the result.

The original I209 brief, report, complete analytic record, and literature note were read. The supplied upper route is nonessential and receives no independent finite-cover approval from this PASS. As a scoped check, its positive-penalty expression F_d/a^4=-1/2+(29/30)z+c(1/z-1), c=2/(3sqrt(3)), satisfies the stated positivity estimate; its affine wall-tangent rigidity calculation also checks. These confirm the limited reported failure of that attempted saving. I have not independently certified every inverse-label/cap estimate or I203's nonlinear theorem, and found no upper-route error requiring a change to the lower proof. The lower proof has no dependence on those assertions, on b:lattice, or on any upper-cover theorem.

No implication for arbitrary affine images or for sum |B_i|/|projection_(u_i-perp) T| is drawn. The directionwise denominators differ; the absolute-area proof does not establish the stronger normalized claim. No assertion about worldwide priority, a best-known bound, contribution status, or count is made.

## 6. Reading and execution limits

The authentication file records hashes and complete read scopes. Existing primary copies were read in place; no new source copy was needed. The Bezdek–Litvak read is exactly PDF pages 1–7 through text extraction, including Theorem 3.1 and its proof; pages 8–14 were not read. All four companion introductions, the two named projection sections, and angular-cubic-buffer.tex were fully read, but not their entire parent manuscripts. These scopes justify the source comparisons only within the statements actually read. The I209 source note's broader prior reading and search claims are not adopted as this review's own.

An initial combined catalogue display was truncated; no full-catalogue read is claimed. The complete targeted catalogue read was sources/CONTENTS.md lines 2435–2490 (Result 100 and its four entries, with adjacent context). No other active review or I203 live output was opened. No source tree, history, or ancestor was inspected.

A partial review and partial authentication/literature records were written before the substantive review was complete. Only the three authorized I211 files were written. No subordinate agents, research code, numerical experiments, parameter scans, tests, snapshots, seals, historical replay, staging, commits, or publication were used. Detached final output hashes are returned in the handoff, not recursively embedded here.
