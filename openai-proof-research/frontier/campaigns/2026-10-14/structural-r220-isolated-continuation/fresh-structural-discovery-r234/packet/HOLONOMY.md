# Stronger integrated reduction: route the twists, do not stop at the first cycle obstruction

This continues the prefreeze derivations in CONSTRUCTION.md. The direction remains one Source358 controlled gluing family. There is no frozen nominee and no claim of literature novelty or substantiality. The primary input is the actual translation-holonomy construction in Leeb section2.3, together with the source's complete cometric and passage proofs.

## 1. The classical freedom available in a surface product

On Sigma_v x (R/Z), let h_{v,e} be the canonical oriented boundary classes and f_v the fiber. A circle-valued smooth function F:Sigma_v->R/Z with degree s_{v,e} on boundary e exists for any INTEGERS s_{v,e} satisfying

    sum_{e incident v} s_{v,e}=0.                     (H1)

Indeed, the boundary classes have just this relation in H1(Sigma_v;Z); assign the proposed values and arbitrary values to handle generators. This integral cohomology class is represented by a map to S^1. One can see the extension explicitly on a surface cell decomposition: the attaching word of the two-cell has total degree zero, so the circle map on its boundary extends. Smooth it relative to collars, on which set F=s_{v,e} theta_{v,e}+constant. The circle-valued shear

    (x,theta_f) -> (x,theta_f+F(x))

is a smooth diffeomorphism. Equivalently alpha=dF is a closed one-form with period s_{v,e}, and

    g_v = g_Sigma + L_v^2(dtheta_f+alpha)^2            (H2)

is locally a product, globally isometric to the product by that shear. Its horizontal boundary direction is the REAL/INTEGRAL vector h'_{v,e}=h_{v,e}-s_{v,e} f_v. In the real-valued version of Leeb's construction s_{v,e} can be any real numbers with zero sum, giving a translation representation; the integer subcase already suffices here. No global exact real potential is assumed for alpha.

Near a boundary alpha=s dtheta_h, so the transformation is exactly linear there. Thus (H2) changes neither local curvature estimates nor collar jets. It also transports any buffered surface-patch product argument from CONSTRUCTION.md section6 by a genuine local isometry. This is stronger than pretending each boundary must be orthogonal to the canonical section individually.

## 2. Track both endpoint changes before choosing them

For a canonical edge u->v with

    h_v=m_e h_u+f_u,          f_v=h_u,

write s_u,s_v for the two boundary shears and h'_u=h_u-s_u f_u, h'_v=h_v-s_v f_v. Direct substitution gives

    f_v=h'_u+s_u f_u,
    h'_v=(m_e-s_v)h'_u + [1+(m_e-s_v)s_u]f_u.         (H3)

Thus in general the right fiber no longer equals the left horizontal direction. Ignoring this term would falsely retain the source neck normal form. To stay within the actual source mechanism, impose s_u=0 at EVERY OUTGOING boundary. Then

    f_v=h'_u,          h'_v=a_e h'_u+f_u,
    a_e=m_e-s_v.                                      (H4)

At each vertex the remaining condition (H1) is exactly

    sum_{e ending at v} a_e = D_v,
    D_v=sum_{e ending at v} m_e.                      (H5)

This is a charge redistribution constraint, not independent freedom in every edge. For a simple directed cycle with one incoming edge at every vertex and m_e>=1, (H5) forces a_e=m_e. The first cycle obstruction really survives in that case within this exact family. But it does NOT survive for all graphs containing a directed cycle.

## 3. A spanning forest solves every simultaneous constraint in a large class

Assume the finite directed graph has the following property: every vertex is reachable by a directed path from a vertex of indegree zero. Call these vertices roots. This property is explicitly nonempty (every acyclic orientation qualifies) and also permits many directed cycles.

Choose a spanning directed forest rooted at these roots, with exactly one chosen incoming edge p(v)->v for every nonroot vertex. For instance take shortest directed distances from the set of roots and choose an incoming edge decreasing distance by one. Set

    a_e=D_v if e=p(v)->v is the chosen parent edge;
    a_e=0 on every other edge ending at v.             (H6)

All m_e are positive integers, so all D_v at nonroots are positive integers. Equations (H5) hold. Define s_v=m_e-a_e at each incoming incidence and s_u=0 at each outgoing incidence. Their vertex sums are zero, so section1 realizes ALL these integer shears simultaneously. In these product coordinates the gluing has a positive shear ONLY on the spanning forest; every remaining edge is a pure flip. This is an actual compatible construction, not a conditional bridge.

## 4. Pure flips and small shears use the full paid cometric estimates

The source writes epsilon=delta^2, but every operative estimate in its cometric proof uses only |epsilon|<=delta^2, fixed cutoff chi, and small delta. More precisely set

    H(t)=e2+epsilon chi(t)e1,
    P(t)=(1+delta A(t))e1 e1^T
         +(1+delta A(1-t))H(t)H(t)^T.                 (H7)

For 0<=epsilon<=delta^2 and 0<delta<=delta_*, the same R=(e1,H) norm bounds hold, E'=O(epsilon), E''=O(epsilon), and hence E''=O(delta^2). On the central interval -P0''>=m delta Id absorbs that error exactly as in the source. Outside it H is constant and a^2<=-a' gives the same domination |P'p|^2<=C delta p^T(-P'')p, INCLUDING null directions. At each endpoint in its own frame the exact cometric is diag(1+delta A(tau),b_delta), independently of epsilon. Therefore the derivative slopes, convex collars, timing beta, mixed S bound proportional to |p1|, dual minimization, returning estimate, all passage classification, and global assembly carry over with the same delta_*.

This is not a new positivity technique: it uses the complete source estimates on the larger range they actually control. In particular epsilon=0 gives a diagonal neck with the right endpoint frame (e2,e1), hence a PURE FLIP with arbitrary positive periods B1,B2. It DOES NOT require delta=0, and it DOES NOT require either torus period to vanish.

Fix one 0<d<delta_* for every neck. Set b=1+d A(1), Dmax=max_v D_v. On a chosen rooted forest let depth(v) be its nonnegative integer depth and choose

    0<q<min(1,d^2/Dmax),
    L_v=rho q^{depth(v)}.

For edge e:u->v put B1_e=L_v sqrt(b), B2_e=L_u sqrt(b), and

    epsilon_e=a_e L_v/L_u.                            (H8)

On a forest edge, epsilon_e=D_v q<d^2. On every remaining edge, epsilon_e=0 REGARDLESS of the ratio of endpoint fiber lengths. The period identity is

    B2_e(e2+epsilon_e e1)=f_u+a_e h'_u,
    B1_e e1=h'_u=f_v.

All assumptions of (H7) hold. Choose rho sufficiently small for every cusp truncation as in CONSTRUCTION.md; all smooth germs match. The holonomy is constant in collar coordinates, so the local product metrics and each neck are exactly the required metrics on open collars. The global geometry is complete because the manifold is compact.

The all-time free-endpoint passage proof, including all zero speeds and all repeated neck/patch visits, is unchanged. In particular this gives smooth no-conjugate-points metrics for EVERY graph satisfying the stated root reachability condition and these canonical positive integral gluings, optionally with the buffered positive surface patches. The proof has executed the compatible classical holonomy operation instead of stopping at the first directed-cycle failure.

There is no asserted unrestricted perturbation neighborhood. The warped-fiber conjugate-field example of CONSTRUCTION.md section9 still applies after conjugating through the circle shear, or simply in a local product neighborhood where alpha has a real potential.

## 5. An explicit cyclic graph that also has the required curvature obstruction

Take n>=3 peripheral vertices 1,...,n and one root 0. Include spokes 0->i for all i, and the directed ring i->i+1 (indices modulo n). Give every edge m_e=1. Each peripheral vertex has one spoke and one incoming ring edge, so D_i=2; D_0=0. Root reachability holds, although the ring is a directed cycle. Give every vertex a surface of genus1, with one boundary for each incident edge.

Choose the spokes as the spanning tree. At vertex i put s=-1 on its incoming spoke, s=+1 on its incoming ring edge, and s=0 on its outgoing ring edge. Their sum is zero. At the root all s=0. Thus the effective spoke shears are 2 and all ring gluings are pure flips. Choose L_0=rho, L_i=q rho, with 0<2q<d^2. Then the spoke epsilons are 2q and the ring epsilons are zero, all with delta=d. This supplies a concrete nonempty metric regime and exact smooth gluing for this cyclic object.

Now exclude a hypothetical nonpositive-curvature/CAT(0) metric using the ORIGINAL canonical boundary classes, since those describe the actual topology independently of the constructed metric. Let x_i=ell_i^2>0 be the hypothetical squared fiber translation lengths, c_{0i} the spoke fiber inner products and c_i the ring fiber inner products. As in CONSTRUCTION.md section7, character sums and lattice independence give

    sum_i c_{0i}=0,
    c_{0i}+c_{i-1}+c_i+2x_i=0,
    c_i > -sqrt(x_i x_{i+1}).                         (H9)

Summing the peripheral equations and using the root equation gives

    0=2 sum_i c_i+2 sum_i x_i
      >2 sum_i x_i-2 sum_i sqrt(x_i x_{i+1})
       =sum_i (sqrt(x_i)-sqrt(x_{i+1}))^2 >=0.

The strict inequality holds for every ring edge because its fiber vectors are independent in its rank-two lattice, regardless of whether the rightmost squares vanish. This contradiction excludes ALL hypothetical positive fiber lengths and not merely the lengths chosen in section4. Thus each wheel-type graph manifold has the same separation of metric-existence categories, with the stronger classical action/no-focal consequences stated and credited in CONSTRUCTION.md section7.

This is a direct graph charge calculation, not inheritance of the two-piece obstruction by a quotient or by an arbitrary covering. The underlying construction is still wholly within the one Source358 family and its actual classical antecedents.

## 6. Distinct types are measured, not presumed

For this graph there are V=n+1 vertices and E=2n edges, so beta1(G)=n. With all genera1 the free handle/stable-letter summand in (8.1) has rank 2(n+1)+n=3n+2. The remaining presentation matrix is

    A = [[0, 1^T], [1, B]],      B=2I+Adj(C_n).

For ODD n, z^T B z=sum_i(z_i+z_{i+1})^2, so B is positive definite: equality forces alternating z around an odd cycle and hence z=0. Also B 1=4 1, so the Schur complement is -1^T B^{-1}1=-n/4, nonzero. Thus A is invertible over Q and

    b1(M_n)=3n+2              for odd n>=3.

These manifolds have pairwise different first Betti numbers, so they are not homotopy equivalent or homeomorphic to one another. They are not asserted pairwise noncommensurable. For n=3, A has determinant -3 and the free rank is11; this is a concrete example distinct from the source's rank4. Nothing in this paragraph makes an infinite parameter selection automatically substantial.

## 7. What this resolves and what it leaves unpaid

The untwisted directed-cycle obstruction in CONSTRUCTION.md is now explicitly qualified: root-accessible cycles CAN be handled after executing classical boundary holonomy, routing their twists onto a tree, and using the zero-shear case actually controlled by the source estimates. No conclusion rests on failure of that naive construction.

For a source strongly connected component with no indegree-zero vertex, this routing argument has no roots. Real rather than integral boundary holonomy still satisfies the exact equations (H3)-(H5), so it does not simply provide independent free boundary shifts. The single directed cycle with one incoming edge at every vertex is the clearest unresolved construction target: (H5) fixes its positive residual shears and the small-shear period product is impossible. No alternative all-passages construction for that object is supplied here; the failure of this particular controlled-cometric family is NOT a nonexistence theorem for no-conjugate-points metrics.

The original source, Leeb's full compatible holonomy, Gulliver's buffered modification, and the elementary boundary-character algebra together close the root-accessible construction above. After those operations are credited, this round has not isolated and proved an additional nonroutine operation warranting a substantial nominee. These derivations are retained as PREFREEZE research, with no correctness/contribution/acceptance/count assigned. No worldwide-priority or exhaustive-history claim is made.
