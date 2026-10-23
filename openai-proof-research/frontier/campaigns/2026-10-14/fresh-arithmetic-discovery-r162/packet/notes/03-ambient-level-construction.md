# Prefreeze calculations II: nearby levels and the quantitative interface

The target remains the entire ambient function in note00, including the double-point and log-canonical branches. We now carry the available nonzero-level construction further than the source's compactness argument. The endpoint is an explicit quantitative interface, not a conditional nominee.

## 1. A uniform relative gradient inequality and finite-length collapse

Let G(x,u) be the covered family (or the original one). The source's Lê–Saito–Teissier estimate gives |G_u|/||d_xG|| -> 0 at the section. Shrink so that ||dG|| and ||d_xG|| are uniformly comparable. Apply Bierstone–Milman Proposition6.8 to the REAL analytic function Q=|G|^2 near (0,0). Its real gradient norm is a fixed conventional constant times |G| ||dG||. Thus, for some 0<lambda<1 and c>0, after replacing the exponent by a larger one below1 if necessary,

    ||d_xG|| >= c |G|^lambda.

The estimate is uniform in the small parameter disk. This uses the full analytic function and the actual small-o comparison; separate gradient inequalities for each fiber with unspecified constants would not suffice. Put theta=1-lambda>0.

On G≠0 define the real spatial vector field in complex notation

    Y(x,u)= G(x,u) overline(d_xG(x,u))/||d_xG(x,u)||^2,
    du(Y)=0.

Then dG(Y)=G and ||Y||<=c^(-1)|G|^theta. For its inward flow, dG/ds=-G, so G(s)=e^(-s)G(0), and

    length from s to infinity <= (c theta)^(-1)|G(0)|^theta e^(-theta s).   (1)

This gives a limit on G=0. On sufficiently small representatives it stays in the domain, since the TOTAL remaining displacement is bounded by the right side. The limit defines a continuous retraction R_u onto the zero fiber: on a finite initial time interval dependence is smooth off G=0, and the uniform exponentially decaying tail proves continuity, including when initial G tends to zero. This proves an estimate to ONE endpoint,

    |x-R_u(x)| <= C |G(x,u)|^theta,                                  (2)

not a two-point Hölder bound for R. Its fibers can contain vanishing-cycle data and it is not an invertible coordinate map.

For an exact closed-ball tube one can modify Y away from a smaller ball using the boundary submersion (G,u). Choose a smooth real right inverse of dG tangent to the sphere, apply it to the vector G in the value plane, and patch to Y. All patches retain dG(Y)=G. On the compact outer region their norm is O(|G|), hence also O(|G|^theta), with theta decreased to <=1. This gives (1) throughout the tube and keeps the sphere invariant. No quantitative statement about the derivative of the resulting flow has yet been made.

## 2. Keep the actual attaching data, not only Milnor-fiber homology

Fix a sufficiently small positive eta. Let

    M_u={x in B: |G(x,u)|=eta}.

This compact manifold with boundary carries the angle map G/eta to S^1. The inward flow defines E_u(m,s), m in M_u and s>=0, with

    G(E_u(m,s),u)=eta e^(-s) G(m,u)/eta.

Every point of the punctured-value tube has a unique (m,s): flow outward, retaining a nonzero value until eta is reached. On each finite time strip this is smooth and reversible. The uniform length estimate extends E_u to s=infinity, defining a continuous attaching map a_u(m)=R_u(m). The CLOSED tube {x in B: |G(x,u)|<=eta} is the quotient of M_u x [0,infinity] by the equal-a_u relation at infinity. Surjectivity onto smooth zero points follows by starting along a small normal value direction and flowing outward; surjectivity onto the origin follows by compactness and (2). Thus this is a genuine description of the zero attachment as well as the nonzero levels.

The smooth proper family M_u has ordinary smooth transport preserving the angle map. But an arbitrary such transport k_u:M_0->M_u need not satisfy

    a_u k_u = z_u a_0,                                               (3)

where z_u is the resolved zero-family map from note02. The map a_u is typically many-to-one. Constancy of mu, the homotopy type of a Milnor fiber, its link, or its monodromy does not supply the equality (3). Conversely an appropriate compatible k_u, with quantitative flow-chart estimates, would give the desired ambient map by E_u(k_u(m),s). This is exactly why the full function-preserving interface has more content than zero-set transport.

The source ALREADY gives a continuous ambient H_u. It therefore gives, for every finite s, angle-preserving maps

    k_(u,s) = E_u(·,s)^(-1) H_u E_0(·,s): M_0 -> M_u.                (4)

These are well-defined homeomorphisms; in the resolved branch the Section13 choices are smooth off the section and give diffeomorphisms at each finite s. The split double-point construction is not silently assumed smooth on every ambient point off the origin. Equation(4) identifies all finite level data, so there is no missing topological existence assertion. However it supplies neither a limiting k_(u,infinity) nor polynomial estimates for its dependence on small values. The source's reverse-transport compactness proof is entirely consistent with highly distorted k_(u,s). We do not replace its actual proven H by an unproved metric version.

King's actual proof retains analogous Milnor-fibration/zero-fiber attaching data. Its Theorem1 requires a parametrized ambient zero-set equivalence; its canonical constructions assert continuity, not a bound for (4). Our intrinsic Hölder map z is insufficient to invoke a quantitative theorem that King does not state.

## 3. Where the naive derivative estimate loses every positive exponent

A direct estimate for Y has the form

    ||D_xY|| <= C(1+ |G| ||D_x^2G|| / ||d_xG||^2).

On a compact representative the Hessian is bounded. The preceding gradient inequality only turns this into

    ||D_xY|| <= C(1+|G|^(2theta-1)).                                (5)

When theta<1/2, write kappa=1-2theta>0. Along an inward trajectory, |G|=eta e^(-s). Integrating the variational inequality gives an upper estimate of the form

    ||D E_u(·,s)|| <= C exp(C e^(kappa s)),                         (6)

with analogous losses when differentiating in parameter. In terms of c=eta e^(-s), this is exp(C |c|^(-kappa)), not a finite power of 1/|c|. The estimate is an upper bound and does NOT prove the actual flow has this growth. It shows exactly why this available calculation does not prove a Hölder estimate. The classical gradient exponent need not satisfy theta>=1/2. Even a sharp one-point length bound (1) cannot be silently substituted for a two-point variational bound.

The same problem occurs for the source's ambient parameter field V. On each fixed nonzero level the time interval is finite and its compactness gives a finite Lipschitz constant. Those constants can grow as the value tends to zero. Merely replacing the partition of unity by a controlled smooth partition with polynomial derivative bounds does not solve the problem: exponentiating a polynomially divergent derivative bound is the mechanism in (6).

## 4. Two usable sufficient estimates, with their exact exponent arithmetic

One possible route is a bilateral radial-and-derivative estimate for an ACTUAL ambient map H, not just its generator. Suppose in product Euclidean coordinates, uniformly in parameter,

    |H_u(x)| <= C |x|^a,
    ||D_(x,u)(H_u(x),u)|| <= C |x|^(-b), x≠0,                    (7)

and corresponding estimates for the inverse, with positive a<=1 and b>=1. Then H is Hölder with exponent a/(a+b), or the smaller of the forward/inverse exponents.

To see this, compare (x,u),(y,v), set d=|x-y|+|u-v| and r=min(|x|,|y|). If d>=r/2, both spatial radii are <=3d and the radial estimate gives C d^a (including the retained parameter coordinate). If d<r/2, a straight product segment stays at radius >=r/2. The derivative estimate gives C d r^(-b), whereas radial control and the parameter difference give C r^a. Therefore

    |H(x,u)-H(y,v)| <= C min(r^a,d r^(-b)) <= C d^(a/(a+b)).     (8)

Use smaller ball/polydisk domains so the segment lies inside the representative. Inverse estimates use the target spatial radius and a smaller ambient ball contained in the image, followed by germ restriction. In particular, a pointwise estimate at the axis plus a polynomial bound for the MAP derivative would suffice. A polynomial bound for the FIELD derivative is a different assertion and only yields exponential Gronwall constants.

A second sufficient route is a true two-point log-Lipschitz modulus for the chosen parameter fields:

    |V(z)-V(z')| <= L d(1-log d), 0<d<1.                         (9)

For trajectories, d'<=L d(1-log d). Put q=1-log d. Then q'>=-Lq and

    d(s)<= exp(1-e^(-L|s|)) d(0)^(e^(-L|s|)).                   (10)

Apply the same estimate to reverse time and compose the two real parameter transports. This supplies a positive joint exponent after keeping the parameter as a coordinate. Note02 then handles the finite cover. Neither the source nor the actually read Parusinski proof supplies (9) for arbitrary nonlinear mu-constant families. Parusinski's bound |g|<=C|x||grad F| controls radial speed, not (9).

## 5. Status of the full construction

The spatial finite-jet reduction is paid. In the source's non-lc resolution branch, analytic equal-fiber separation pays joint intrinsic bi-Hölder zero transport, and the explicit seam pays its descent to the original disk. The uniform gradient construction gives finite-length attaching maps for ALL branches and exact continuous identifications at every nonzero value via the existing H, smooth for the resolved branch. No off-axis smoothness is added to the split double-point construction.

The unresolved operation is to choose an ambient function-preserving identification across these attaching maps with bilateral two-point power control. Estimates such as (7), (9), or another construction providing the target's inequalities would close it. A compatible quantitative version of (3)–(4) is one concrete way to seek it; it is not asserted. The low-case Whitney/splitting branch also requires metric control of its actual ambient map; no restriction to non-lc inputs is being substituted for note00. Ordinary qualitative transport, arbitrary unmarked Milnor-fiber identifications, and a zero-locus Hölder estimate are insufficient to settle the unchanged full target.
