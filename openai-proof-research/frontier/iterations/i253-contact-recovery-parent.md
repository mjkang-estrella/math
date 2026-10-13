# I253: nonlinear recovery for the nested ball–tube contact problem

2026-10-12. Parent follow-up to completed I249. **Technical progress only; no accepted-count change.** The nonlinear lower bound remains unproved.

## Statement

Use exactly I249's unit cubic torus, fixed R in (2/9,1/pi), r=R-e, volumes a=4pi R^3/3 and b=pi r^2, and deficit D_R(e) over all finite-perimeter pairs E subset F of those volumes. Let

    G_R=R^2-(R/2)cot(1/(2R)),
    K(R)=4pi R/(R+4G_R).

Conditional only on I249's explicitly proved quadratic minimization (not its unproved nonlinear target), the matching nonlinear recovery bound is

    limsup_{e downarrow 0} D_R(e)/e^2 <= K(R).

This replaces I249's weaker explicit ellipsoid bound 8pi. It does not prove the proposed limit or provide independent validation of I249's quadratic calculation.

## Smooth strict-obstacle approximation

The quadratic minimizers in I249 are rotationally invariant Lipschitz normal displacements

    u_*(t)=A_*(1-2|t|),       t=cos(phi) on S_R,
    v_*(z)=D_* g_R(z)/G_R,    z in R/Z,

with separate zero means and v_*(0)-u_*(0)=1. Their quadratic energy is K(R). Smooth them as even axial functions, near t=0 for u and periodically for v. Subtract their respective means. This gives smooth u_j,v_j converging uniformly and in H^1 to u_*,v_*. Smoothness at the poles is retained because u_* is already smooth there and the sphere mollification is confined away from them.

Fix eta>0. The traces v_j(0)-u_j(0) converge to one. Multiply both smoothed functions by

    c_j=(1+eta)/(v_j(0)-u_j(0))

for sufficiently large j. The resulting functions, still denoted u_j,v_j, have zero means, strict trace gap 1+eta, and quadratic energy tending to (1+eta)^2 K(R). Here H^1 convergence of these particular Lipschitz profiles and their uniform convergence are obtained directly by mollification; no point-evaluation assertion for general two-dimensional H^1 functions is used.

Fix one such smooth pair u,v. All constants and small-e thresholds in the next steps may depend on this pair and eta. This order of limits is essential.

## Exact volumes

Let E_e be the radial graph over the sphere with radius

    R+e u(omega)+s(e).

Choose s(e) so that E_e has volume a. The volume is (1/3) integral over the unit sphere of this radius cubed. Its derivative in s at zero is 4pi R^2. The zero mean of u eliminates its first-order variation, so the implicit function theorem gives s(e)=O(e^2).

Let F_e be the periodic tube with radius

    R-e+e v(z)+t(e).

Choose t(e) to have volume pi(R-e)^2. Its volume is pi integral_0^1 [R-e+e v(z)+t(e)]^2 dz. The derivative in t at zero is 2pi R, and the zero mean of v again gives t(e)=O(e^2). Both radii are positive and less than 1/2 for small e; the sphere remains embedded. Thus the prescribed volumes and ambient torus geometry are respected exactly.

## Nonlinear inclusion

At a point of the sphere graph with latitude t, its axial coordinate is

    z_e(t)=[R+e u(t)+s(e)]t

and its transverse radius is [R+e u(t)+s(e)]sqrt(1-t^2). The margin inside F_e is therefore

    Delta_e(t)=R-e+e v(z_e(t))+t(e)
                    -[R+e u(t)+s(e)]sqrt(1-t^2).

At e=0 this equals R[1-sqrt(1-t^2)], positive away from t=0. Its first-order coefficient at t=0 is v(0)-u(0)-1=eta>0. More explicitly,

    Delta_e(t)=R[1-sqrt(1-t^2)]
          +e[-1+v(Rt)-u(t)sqrt(1-t^2)]+O(e^2),

uniformly for t in [-1,1]. Uniformity follows from the fixed smooth v, bounded u and the volume-correction estimates; no derivative of sqrt(1-t^2) is taken here.

By continuity choose tau>0 so the bracket is at least eta/2 for |t|<tau. On that strip Delta_e is positive for small e. Outside it the positive zeroth-order margin dominates the bounded first-order term. Thus the entire boundary of E_e lies inside F_e. Rotational symmetry makes every horizontal slice of F_e a disk centered on the axis; the maximal transverse radius of a slice of E_e is reached on its boundary. Hence E_e subset F_e, not merely inclusion of their traces at the contact circle.

This strict-buffer construction avoids trying to impose the limiting equality constraint directly on nonsmooth profiles. An O(e^2) volume correction cannot defeat its O(e eta) positive margin.

## Perimeter expansion and limits

The smooth area formulas and exact volume corrections give

    P(E_e)=4pi R^2+(e^2/2) Q_B(u)+o(e^2),
    P(F_e)=2pi(R-e)+(e^2/2) Q_C(v)+o(e^2),

where Q_B and Q_C are exactly I249's volume-constrained Jacobi forms at S_R and Z_R. The cylinder base radius is R-e; replacing it by R in the quadratic coefficient changes only o(e^2). For example, its exact volume correction t(e)=-e^2 integral v^2/(2R)+O(e^3) supplies the negative term in Q_C. The sphere correction similarly supplies the negative 2/R^2 term in Q_B. There is no first-order perimeter term after each exact volume is matched to its reference surface.

For each fixed j,eta these admissible sets imply

    limsup D_R(e)/e^2 <= [Q_B(u_j)+Q_C(v_j)]/2.

Now let j tend to infinity, then eta down to zero. This gives the claimed upper bound K(R). No uniform Taylor remainder over j and no exchange of these limits is required: every fixed j is an independent upper bound on the same limsup.

## Remaining work

The missing lower bound concerns arbitrary finite-perimeter near-minimizing pairs. It requires an inclusion-preserving regularization and a common normalization that yield the limiting contact trace constraint and the Jacobi-energy lower bound. Separate one-interface stability is insufficient. In particular this recovery construction says nothing about tentacles, contact concentration or relative-center scales in an arbitrary minimizing sequence.

The source premises, quadratic minimizers and primary comparison are those in [I249's full analytic note](../experiments/i249_geometric_analytic_discovery/analytic-attempt.md), which the parent read in full. This follow-up contains only the nonlinear recovery construction and is not represented as an independent substantial finding or as a completed asymptotic theorem.
