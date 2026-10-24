# Integrated prefreeze construction: compatible graph necks and buffered surface patches

These are durable research derivations, not a frozen author-proof nominee, manuscript, or independent review. All Source358 operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. The construction below credits them in full. Its purpose is to execute the strongest compatible combination before deciding what additional operation remains.

## 1. Fixed interfaces and what can actually vary

Write P_delta for the exact source cometric, b_delta=1+delta A(1), epsilon=delta^2, and ell_delta for its convex collar warp. Let delta_* be a positive upper bound satisfying BOTH the source cometric lemma and the turning-delta-choice inequality. Shrink it below 1 if necessary. No numerical value of delta_* is needed, and no numerical sample substitutes for its proved uniform inequalities.

The metric of one neck is dt^2+dx^T P_delta(t)^{-1}dx. In the left frame (e1,e2) the surface coordinate has period B1 and the fiber coordinate period B2. In the right frame (e2+delta^2 e1,e1), these periods are B2 and B1 respectively. The fiber lengths are B2/sqrt(b_delta) and B1/sqrt(b_delta), since the endpoint fiber metric coefficient is b_delta^{-1}.

More generally, fix an integer m>=1 and set B1=(delta^2/m)B2. Then the right surface period vector is

    B2(e2+delta^2 e1) = f_u + m h_u,
    B1 e1 = h_u.

Thus exactly the same LOCAL cometric, with exactly the same paid estimates, realizes the integral gluing

    h_v = m h_u + f_u,       f_v = h_u.                 (1.1)

The matrix [[m,1],[1,0]] has determinant -1 and is unimodular. In particular these two period vectors generate the very same lattice, not a proper sublattice. The two actual fiber lengths must satisfy

    delta_e^2 = m_e L_v/L_u.                            (1.2)

This is the first simultaneous constraint. All boundary circles of one product piece must use one common L_v. Independent edge parameters generally fail this constraint.

For a directed cycle, multiplying (1.2) gives

    product(delta_e^2) = product(m_e) >= 1.

Since every admitted delta_e<1, such a cycle cannot be realized by this particular family of necks and untwisted product cores. This is an obstruction to THIS ANSATZ, not a theorem that a graph manifold with such a cycle has no metric without conjugate points.

For any finite directed acyclic graph, the constraints have explicit solutions. Choose a strictly increasing integer rank r(v) along arrows, put M0=max_e m_e, choose

    0<q<min(1,delta_*^2/M0),
    L_v=rho q^{r(v)},
    delta_e=sqrt(m_e q^{r(v)-r(u)}) for e:u->v.         (1.3)

Then 0<delta_e<delta_* for every edge and (1.2) holds. The common factor rho>0 is reserved for fitting the surface cusps. In particular the parameter regime is nonempty. There is no asserted positive lower bound on delta_e as the graph, ranks, or q vary.

## 2. All interfaces in the graph are matched simultaneously

Let G be a finite connected loopless graph with at least one edge, given an acyclic orientation; multiple edges are allowed. For each vertex choose an oriented compact surface of genus g_v>=1 with d_v=deg(v) boundary components, one labelled by each incident edge. These surfaces have negative Euler characteristic. Use the product with a circle, and orient every boundary curve h_{v,e} as the boundary of that surface. Give every circle the same orientation used in (1.1). The boundary gluing maps are orientation reversing, so pairing all boundaries produces a closed connected orientable smooth 3-manifold. Finite cylinders inserted at the seams do not change its diffeomorphism type.

Choose, once for each vertex, a complete finite-area hyperbolic surface of genus g_v with d_v cusps and disjoint cusp charts. Such a surface can be made by a pants decomposition: internal geodesic boundary lengths can all be fixed to 1 and the d_v external boundary lengths taken to zero. Hyperbolic pants arise by doubling right-angled hexagons, with zero-length sides giving ideal vertices/cusps. Internal geodesic seams have identical Fermi germs dr^2+cosh^2(r)dy^2, so their gluings are smooth. This supplies the required finite number of disjoint cusp ends, each with metric dr^2+c_{v,e}^2 exp(-2r)dtheta^2. It also leaves fixed compact regions away from all cusps. This is the ordinary hyperbolic-surface construction underlying the flexibility in Leeb section2.3, not a new geometric operation.

On edge e:u->v use delta_e from (1.3), and set

    B2_e=L_u sqrt(b_e),       B1_e=L_v sqrt(b_e).

Equation (1.2) gives delta_e^2 B2_e=m_e B1_e as required. At the tail cusp truncate at horocycle length B1_e ell_e(-1); at the head cusp truncate at length B2_e ell_e(-1). These lengths are all positive multiples of rho. There are only finitely many cusp ends, so a single sufficiently small rho makes every truncation lie in its prescribed embedded disjoint cusp chart. This choice does not change delta_e or ANY neck estimate.

Attach the collar [-1,0] with metric d tau^2+ell_e(tau)^2dy^2 and with surface coordinate period B1_e at the tail and B2_e at the head. The identity

    ell_e(tau)=ell_e(-1)exp(-(tau+1)) near -1

matches the hyperbolic metric on an OPEN neighborhood, under r=r_{v,e}+tau+1 and theta=y/B. At tau=0, the collar warp equals (1+delta_e A(tau))^{-1/2} on an OPEN neighborhood. These are exact germs, so every jet matches; no partition of unity is used.

Give the vertex circle the metric L_v^2 dtheta_f^2, theta_f modulo 1. In each incident neck frame take y_f=B_f theta_f, where B_f=L_v sqrt(b_e). Then b_e^{-1}dy_f^2=L_v^2dtheta_f^2. Therefore even when distinct incident edges have different delta_e and b_e, they induce the SAME circle metric at that vertex. The surface collar changes from boundary to boundary; the fiber metric does not. The maps (1.1) finish the smooth gluing. Positive definiteness is the source's proved 1/9<=P<=18 estimate in each frame, together with positive collar warps and product metrics.

This gives the complete source-type metric on the graph, before any surface blister. There are no unpaired boundaries or infinite accumulations in the manifold construction.

## 3. Repeated visits, not just a single neck calculation

Let U be the union of the finitely many open necks. For an arbitrary complete unit-speed geodesic gamma and smooth compactly supported field V, every component of gamma^{-1}(U) belongs to one neck. Its maximality is exactly the maximality required by the source passage estimate: the necks are disjoint and separated by core regions. The universal lifted metric on that neck is precisely a source metric with its admitted delta_e; only lattice periods changed.

The source's full classification and proof therefore cover:

* zero torus momentum (a transverse crossing), nonzero momentum, and the limiting small incidence directions;
* a complete constant-height trajectory trapped in a neck;
* monotone half-infinite trajectories tending to equilibria;
* finite crossings; shallow returns contained in the nonpositive-curvature end collars;
* deep returns, with arbitrary duration and arbitrary ORIGINAL endpoint field values;
* tangent interface trajectories, which are outside the open neck unless the source's transversality condition holds.

In each case the original intrinsic normal index is nonnegative. Tangential gauges are used only to prove that unchanged number and are never glued into a global field. Off U the curvature is nonpositive, so its index density is nonnegative. Countable additivity of the absolutely integrable compactly supported index density sums all visits, even infinitely many visits accumulating in a finite interval. This is precisely the paid source global-assembly proposition, applied to a finite union of necks. Its index criterion handles all Jacobi fields, not only transverse generic ones; longitudinal fields, constant geodesics, and affine reparametrizations are included by that criterion. The graph metric has no conjugate points.

This assembly is fully available from the source. Replacing one neck by finitely many is not an unpaid global-Jacobi operation.

## 4. Exact scalar free-endpoint estimate for a buffered positive patch

The strongest relevant Gulliver1975 operation is a positive-curvature cap with negatively curved buffers, INCLUDING all repeated encounters. It is not merely a one-pass or finite-time statement. Here is a direct variational version that exposes its compatibility with the source's free-endpoint assembly.

Let b>0, r>0, R>0 satisfy

    br<pi/2,       a:=tanh(R)>b tan(br).                (4.1)

Consider a finite geodesic passage whose middle interval has length T<=2r and curvature at most b^2, and whose left and right intervals have lengths R1,R2>=R and curvature at most -1. Additional intervals of nonpositive curvature may be appended outside. For every real H^1 field coefficient w, with NO endpoint restriction, the scalar index is nonnegative.

First, for a buffer [0,s] whose inner endpoint value is z, minimizing

    integral_0^s (w'^2+w^2)

with w(s)=z and the outer endpoint free gives w(x)=z cosh(x)/cosh(s). Direct integration, or completing the square with this positive solution, yields

    integral_0^s(w'^2+w^2) >= tanh(s) z^2 >= a z^2.    (4.2)

This is also valid at s=R; no uniform upper bound on s is assumed. The natural boundary condition at the free endpoint is w'(0)=0, NOT a zero value.

On the middle interval [0,T], let u(t)=cos(b(t-T/2)); u is strictly positive by (4.1). Direct expansion and integration by parts give

    integral_0^T(w'^2-b^2 w^2)
      = integral_0^T u^2 ((w/u)')^2
        - b tan(bT/2)(w(0)^2+w(T)^2).                 (4.3)

Both endpoint signs are negative: u'(0)/u(0)=+b tan(bT/2), while u'(T)/u(T)=-b tan(bT/2). Combining (4.2) and (4.3), the full index is bounded below by

    integral_0^T u^2 ((w/u)')^2
       + [a-b tan(bT/2)](w(0)^2+w(T)^2),             (4.4)

plus nonnegative buffer remainders. The bracket is >=eta:=a-b tan(br)>0. It follows that equality for a passage with a positive middle length forces w=0 on the middle and both buffers. The weak nonnegative threshold eta=0 also works for nonnegativity; at the exact symmetric threshold there is a nonzero ground-state equality field. We use the STRICT inequality only.

Every identity is first proved for smooth w, then extends to H^1 by one-dimensional density and bounded potentials on the fixed interval. This is a free-endpoint quadratic-form estimate, not a claim of uniform global coercivity in time, or openness of the no-conjugate-points condition.

For comparison with Gulliver's Riccati calculation, on a buffer p=u'/u evolves by p'=1-p^2, sending 0 to tanh R. A middle segment of length 2r evolves by p'=-b^2-p^2; the initial value b tan(br) is sent to -b tan(br). The second buffer sends every value above -tanh R to a positive value. These are exactly the positive / negative / positive barriers in his section3 argument. Formula (4.4) packages the same strict threshold into a Neumann index statement. It is a classical one-dimensional operation, not evidence of a new contribution by itself.

## 5. Execute the smooth surface modification

Choose finitely many pairwise disjoint hyperbolic disks inside the fixed compact parts of the vertex surfaces. Each disk is away from all cusp/collar seams. It suffices that their radii are some R0>0, with no large-radius requirement unless one separately wants prescribed focal behavior. We do not assert such extra behavior here.

The precise radial interpolation from Gulliver section3 works on each disk as follows. For fixed b>0 and small r1>0, choose r2 by

    sinh(r1-r2)=sin(br1)/b.

For small r1, sin(br1)/b<r1<sinh(r1), so 0<r2<r1. Put G0=sin(br)/b before r1 and G0=sinh(r-r2) after r1; the value matches at r1. The logarithmic derivatives are X0=b cot(br) and X0=coth(r-r2). The second branch is strictly larger at the seam. For small epsilon>0, smooth the change on (r1-epsilon,r1+epsilon), retaining the exact two germs, the curvature upper bound, and the exact integral of X0 over that interval. The last constraint is essential: it makes the outer G equal sinh(r-r2), with no unnoticed multiplicative mismatch.

For completeness, this simultaneous smoothing can be done in the variable k defined by X=b cot(b(r-k)). On a small transition neighborhood, X'+X^2>=-b^2 is equivalent to k'>=0, and X>=b cot(br) follows from k>=0. The hyperbolic target branch k_h is positive and has positive derivative there. Use two smooth nondecreasing cutoffs of k_h, one delayed past r1 and one advanced before r1, each zero before its support and equal to k_h after it. Their associated X integrals lie strictly below and above the step-profile integral. Convex interpolation of the k functions keeps k>=0 and k'>=0, preserves both outer germs, and gives a continuous family of integrals, so the intermediate value theorem imposes the exact integral. Shrinking epsilon keeps 0<r-k<pi/(2b) throughout the transition. This is the original Gulliver interpolation mechanism, now with its matching constraint made explicit.

Define G by G'/G=X and G=sin(br)/b near the center. It is smooth with the spherical polar germ at r=0, G>0 and G'>0 away from the center, Gaussian curvature K=-G''/G<=b^2, and G=sinh(r-r2) for r>=r3:=r1+epsilon. Glue the outer annulus to the original hyperbolic disk by the radial shift r_old=r-r2. At its outer radius R0+r2, the metric agrees on an OPEN neighborhood with the original disk. Thus the modified surface and every cusp collar are C-infinity smooth. No connection or metric averaging is used.

Choose r1 and epsilon so small that

    br3<pi/2,
    R':=R0+r2-r3 > R0/2,
    b tan(br3)<tanh(R0/2).                             (5.1)

This is possible because r2,r1,epsilon,r3 all tend to zero, and the left side tends to zero. Thus (4.1) holds with r=r3 and R=R'. Convexity G'>0 makes radial distance convex along a nonradial geodesic. Any excursion that enters the inner cap crosses a hyperbolic shell of radial width R' on both sides; unit speed makes the shell times at least R'. The cap's geodesic passage has length <=2r3 by Gulliver's Theorem1 comparison (whose proof is read in section2). A trajectory missing the cap sees only curvature -1. Convexity excludes trapping in this disk and makes the passage an interval with these ordered parts; tangencies to the outer sphere do not enter the open disk. All hypotheses of (4.4) hold. This gives nonnegative scalar index for EVERY whole disk passage, allowing arbitrary endpoint values.

The positive cap is a real modification: K=b^2 on a nonempty disk. Its size is chosen by (5.1), rather than inferred from a theorem title. Selecting several disks does not require any claim that disjoint modifications are dynamically independent; the next step treats their visits together with all neck visits.

## 6. Lift the surface patches through the circle factor, including zero-speed fibers

Replace the surface metric as in section5 while retaining its vertex product circle of length L_v. Each modified open disk gives a cylinder W=D x S^1. A geodesic in the vertex product has constant surface speed alpha in [0,1] and constant fiber speed c, with alpha^2+c^2=1. If alpha>0, let E1 be its unit surface direction, E2 the perpendicular surface unit vector, and E3 the unit circle direction. These are parallel along the product geodesic, and

    T=alpha E1+c E3,
    R(E2,T)T=alpha^2 K E2,
    R(E1,T)T=R(E3,T)T=0.

Writing an arbitrary field as x1 E1+x2 E2+x3 E3 gives its FULL index on the cylinder passage as

    integral (x1'^2+x3'^2+x2'^2-alpha^2 K x2^2) ds.

Using surface arclength ell=alpha s, the last two terms have integral

    alpha integral [(d x2/d ell)^2-K x2^2] d ell >=0

by section5 with arbitrary endpoints. The other terms are nonnegative. This argument asserts no bound uniform in 1/alpha and does not divide by alpha when alpha=0.

If alpha=0, the trajectory is a fiber over a fixed surface point, stays in that product for all time, and R(.,T)T=0. Its full index for a compactly supported field is integral |D_sV|^2>=0, even if the base point lies in the positive-curvature cap. This explicitly handles the trapped fiber trajectories and the zero-momentum boundary case. The surface-positive curvature does NOT become positive curvature in a mixed fiber plane of the unwarped product.

Now let U be the disjoint union of all neck interiors and all modified cylinders. Off U the metric still has nonpositive sectional curvature. Each connected component of the preimage of U lies in a single neck or cylinder and has the full free-endpoint intrinsic index estimate already established. Applying the SAME source countable-assembly and index-criterion proof proves absence of conjugate points on the entire closed manifold. It includes arbitrary sequences alternating necks and cylinders, repeated returns, infinitely many visits, and all compact supports. This is the strongest compatible source/Gulliver combination reached here.

## 7. Curvature obstruction for the new graph, not an illicit edgewise reuse

In a hypothetical proper cocompact action of the resulting group on a proper CAT(0) space, the source's semisimplicity argument applies unchanged. Each incompressible boundary torus gives a rank-two translation lattice on a flat. Injectivity follows from the boundary inclusions in negative-Euler-characteristic surface products and graph-of-groups normal form. The product pieces have central fiber f_v. Its centralizer translation character tau_v exists, and on any incident torus satisfies

    <vec(h_{v,e}),vec(f_v)>=ell_v tau_v(h_{v,e}),
    ell_v=translation length(f_v)>0.

The surface relation is product_e h_{v,e} times a product of commutators =1, after basepoint paths. Thus sum_e tau_v(h_{v,e})=0. Basepoint conjugations do not alter this character calculation. These are Leeb's SUM relations. One must not replace them by individual orthogonality at a multi-boundary vertex.

Put x_v=ell_v^2. For an oriented edge u->v let c_e be the inner product of the two fiber translation vectors on its common torus flat, transporting by its gluing conjugation if needed. Formula (1.1) gives the contributions c_e at u and c_e+m_e x_v at v. The flat lattice vectors f_u,f_v are independent: in the edge group f_v=h_u and (h_u,f_u) is a basis. Consequently

    |c_e|<sqrt(x_u x_v),        x_v>0,                  (7.1)
    sum_{e incident v} c_e + D_v x_v=0,
    D_v=sum_{e ending at v} m_e.                       (7.2)

These relations are necessary for the hypothetical action; they are not assumed sufficient for arbitrary graph manifolds. The actual constructed Riemannian fiber lengths L_v need not equal these hypothetical ell_v. Any obstruction must exclude ALL positive x_v, not only the constructed values.

For a bipartite graph oriented from class A to class B with all m_e>0, summing (7.2) on A gives sum_e c_e=0. Summing on B gives sum_e c_e+sum_{v in B}D_v x_v=0. Their difference is a strictly positive sum equal to zero. This excludes the action for every such graph and every choice of its hypothetical metric.

There is also a concrete non-bipartite example with no directed cycle. Take a triangle with arrows 1->2, 1->3, 2->3 and all m=1. Equations (7.2) say

    c12+c13=0,
    c12+c23+x2=0,
    c13+c23+2x3=0.

They imply

    c23=-(x2/2+x3).

But x2/2+x3>=sqrt(2 x2 x3)>sqrt(x2 x3), violating (7.1). Thus the triangle construction has no proper cocompact action on a proper CAT(0) space, in particular no smooth nonpositively curved metric and no locally CAT(0) metric inducing its topology. This proof uses the new graph's own boundary relations; it neither averages a covering metric nor assumes a single source obstruction passes to an arbitrary quotient.

Its compatible neck parameters are especially explicit: choose 0<d<delta_*, set

    L1=rho, L2=d^2 rho, L3=d^4 rho,
    delta12=delta23=d, delta13=d^2.

All collar matching from section2 remains valid, including the unequal b(d) and b(d^2) at vertices1 and3. Thus the obstruction is paired with a genuinely nonempty smooth no-conjugate-points construction, and not an empty set of proposed parameters.

Kapovich-Leeb's actual section2 proves more in the Haken three-manifold category: discrete semisimple actions on complete CAT(0) spaces (not assumed proper) imply a smooth nonpositively curved metric, and this discrete semisimple action property is invariant under passage to finite index. The constructed manifolds are Haken graph manifolds with negative-Euler-characteristic product bases and incompressible tori. Their irreducibility follows by gluing irreducible surface products along incompressible tori (or by the usual innermost-circle sphere argument); hence their hypotheses apply. Therefore the obstruction also excludes such discrete semisimple actions, and excludes nonpositive-curvature metrics on finite covers. This is a CLASSICAL extension, credited to Theorems2.3 and2.4, not a new result here. No assertion excludes arbitrary nonproper actions with parabolic elements. Ivanov-Kapovitch Theorem7.1 likewise gives the no-focal-points obstruction in this closed three-manifold category; it is already paid for the source and routine for this assembly.

## 8. A concrete invariant, without a commensurability claim

In abelianization, the 2g_v handle generators at each vertex are independent; its boundary generators sum to zero. Use (1.1) to eliminate every boundary generator in favor of fibers. The remaining relations are

    sum_{u adjacent v} f_u + D_v f_v=0,

with repeated edges counted. Graph stable letters add a free Z^{beta1(G)} summand. Thus

    H1(M;Z) = Z^{2 sum_v g_v + beta1(G)} direct-sum coker(A),
    A=adjacency(G)+diag(D_v).                          (8.1)

The orientation only enters D_v; A is symmetric. There is no additional relation on handle generators, because the original surface relations become precisely the displayed boundary sums and the edge inclusions involve only boundaries and fibers.

For the triangle with all genera1, A=[[0,1,1],[1,1,1],[1,1,2]], det A=-1, so H1=Z^7. For the original source two-vertex graph with genera1 and m=1, A=[[0,1],[1,1]], det=-1 and H1=Z^4. The triangle is therefore not homotopy equivalent or homeomorphic to the source manifold. Changing genera in this triangle changes the rank 2 sum g_v+1. This is an actual invariant separating the resulting types, but it does not prove noncommensurability, and infinitely many genera are not offered as substantiality evidence.

## 9. Why the extra local freedom does not give unrestricted stability

There is a precise obstruction to promoting the above family to an open set of all smooth metrics. It is stronger than merely noting that no-conjugate-points need not be open.

Any unmodified vertex core contains an open product ball B x S^1. Choose p in B and a compactly supported smooth function phi on B with phi(p)=0, d phi(p)=0, Hess_p phi=-g_surface. For small epsilon>0 let f_epsilon=1+epsilon phi>0 and change the metric on this product neighborhood to

    g_epsilon = g_surface + f_epsilon^2 L_v^2 dtheta^2.

This agrees with the original metric near the support boundary and converges to it in EVERY fixed C^k norm, indeed in the C-infinity topology as epsilon->0. The vertical unit-speed fiber through p is still a complete closed geodesic, since d f_epsilon(p)=0. At p the mixed sectional curvature is

    K(E,T)=-Hess_p f_epsilon(E,E)/f_epsilon(p)=epsilon

for every unit horizontal E. The horizontal directions are parallel along this fiber because the gradient vanishes there. Hence

    J(s)=sin(sqrt(epsilon)s) E(s)

is a nonzero normal Jacobi field with zeros at s=0 and s=pi/sqrt(epsilon). The altered metric has conjugate points. Smooth metrics arbitrarily close to the integrated construction therefore fail the desired property, even while every neck and every seam is untouched. Positive finite-time margins cannot prevent this conjugate time tending to infinity.

This is an explicit failure for arbitrary fiber-dependent/warped perturbations of these product regions. It does not contradict the compatible restricted radial SURFACE modifications in sections5-6, whose mixed fiber curvature remains zero. It is not a claim about every possible metric on the same manifold.

## 10. Exact residual work and decision boundary

The graph construction, free-endpoint buffered-patch inequality, global repeated-visit argument, charge obstruction, and perturbation example above are carried through. They use the complete paid source mechanism and the actual strongest compatible classical operations; none is supported only by a catalogue or an unread named intermediate.

What is NOT established is an additional substantially different operation beyond that composition. In particular, there is no construction for arbitrary gluing matrices or for a rootless simple directed cycle as qualified in HOLONOMY.md, no replacement for the required small cometric shear, no uniform all-time perturbation theorem allowing mixed-fiber curvature, and no new invariant splitting or Anosov conclusion. The explicit perturbation in section9 refutes one natural strengthening at this constructed family. The graph-cycle constraint rules out the most direct free-parameter strengthening of this ansatz. Neither failure proves novelty, impossibility of all alternative constructions, or exhaustion of Source358.

Leeb section2.3 allows nontrivial real translation holonomy of surface loops, constrained only by the sum of boundary values. That stronger classical flexibility is addressed in HOLONOMY.md rather than silently excluded. The ordinary graph and radial modifications above are retained as integrated derivations, not put forward as a substantial full-scope nominee. No frozen target has been weakened, renamed, or submitted for a grade.
