# r212: completed conformal compositions and remaining interface

Research derivations, PREFREEZE. These are comparisons and consequences of the stipulated Source336 operations and the admitted original mathematical construction. No theorem is frozen or nominated, no old scope is amended, and no review grade is assigned. Throughout, M is a connected smooth boundaryless n-manifold, g is smooth and complete, n>=3, Delta=div grad, and all form tests are real functions in C_c^infinity(M). Write

    Q_a,g(phi) = integral_M (a |dphi|_g^2 + Scal_g phi^2) dvol_g.

Scalar curvature can have either sign. The integrals are finite because tests have compact support. A lower form bound below is imposed on this domain, not on an unspecified L2 eigenfunction. Put C_3=500 and let C_n for n>=4 be the dimension-only whole-fiber constant supplied by S. Source targets carry their usual polyhedral topology. All asserted fibers below are ENTIRE inverse images, including disconnected fibers.

## 1. Exact conformal form identity, including the general coefficient

Let rho>0 be smooth, f=log rho, h=rho^2 g, and phi=rho^((n-2)/2) psi. Multiplication is a bijection on compactly supported smooth tests; supports are unchanged. The scalar formula and volume formula give

    Scal_h = rho^-2 [Scal_g - 2(n-1) Delta_g f
                     - (n-1)(n-2)|df|_g^2],
    dvol_h = rho^n dvol_g.

Expanding the gradient of psi=rho^(-(n-2)/2)phi, the cross term in the integral is

    -a(n-2) integral phi <dphi,df>
       = a(n-2)/2 integral (Delta f) phi^2.

There is no boundary term. Consequently

    Q_a,h(psi) = Q_a,g(phi) + integral [A_a Delta f + B_a |df|^2] phi^2,
    A_a = a(n-2)/2 - 2(n-1),
    B_a = a(n-2)^2/4 - (n-1)(n-2) = (n-2)A_a/2.       (1)

Also integral psi^2 dvol_h = integral rho^2 phi^2 dvol_g. In particular,

    Q_4,h(psi) = Q_4,g(phi)
                 - integral [2 Delta f + (n-2)|df|^2] phi^2.          (2)

This is an exact identity; a gradient bound alone does not bound the displayed Laplacian pointwise. It is not conformal covariance of the coefficient-4 operator.

For comparison with a positive density, put D_beta(g,T)=Scal_g+2Delta T-beta|dT|^2. Direct substitution gives

    D_1(rho^2 g, T+(n-2)f)
       = rho^-2 [D_1(g,T)-2Delta f-(n-2)|df|^2].                    (3)

The alternative T+(n-1)f removes Delta f but leaves

    rho^-2 [D_1(g,T)-2<dT,df>-(n-1)|df|^2].                       (4)

Thus a change of density does not by itself remove every uncontrolled error.

## 2. Complete variable-scale geometry and conversion of full fibers

Assume r:M->(0,infinity) is smooth and |dr|_g<=epsilon, for a constant epsilon>=0. Fix b>0, put rho=b/r and h=b^2 r^-2 g. This metric is complete. Indeed, r(x)<=r(o)+epsilon d_g(o,x). For any rectifiable path from o, parametrized by g-arclength s, r at arclength s is at most r(o)+epsilon s. Its h-length is therefore at least

    (b/epsilon) log(1+epsilon L_g/r(o))

when epsilon>0, and b L_g/r(o) if epsilon=0. Taking infima bounds h-distance from below by the same increasing function of g-distance. An h-Cauchy sequence is g-bounded, hence lies in a g-compact set by completeness. On that set both smooth metrics are uniformly equivalent, so the sequence converges also in h. This proves completeness without bounded geometry or a positive global lower bound for r.

Along an h-unit-speed minimizing geodesic gamma from x to y, of h-length L, the chain rule gives

    |(log r(gamma))'| <= epsilon/b,
    length_g(gamma) = (1/b) integral_0^L r(gamma(s)) ds.

Thus

    d_g(x,y) <= r(x) (exp(epsilon L/b)-1)/epsilon,                 (5)

with the continuous interpretation r(x)L/b when epsilon=0. Reversing the curve permits the minimum of the two endpoint radii in (5). A sharper, symmetric calculation, using the minimum of the forward and backward exponential bounds, gives

    d_g(x,y) <= [2 sqrt(r(x)r(y)) exp(epsilon L/(2b))
                    -r(x)-r(y)]/epsilon.                         (6)

Here |log(r(y)/r(x))|<=epsilon L/b ensures the two exponentials cross within [0,L]. Equation (6) is used only for epsilon>0. It is not needed for the conclusions below.

If a continuous source map F has every nonempty h-fiber of diameter <=W, then for every x in that fiber E,

    E subset closed_B_g(x, r(x) (exp(epsilon W/b)-1)/epsilon).     (7)

This is a statement about the whole fiber. It also yields

    diam_g E <= 2 (inf_E r) (exp(epsilon W/b)-1)/epsilon.          (8)

The infimum can either be taken by approximation or attained: E is closed (target Hausdorff), h-bounded, and h is complete, so E is compact. Formula (8) has a factor 2 because (7) is an anchored radius bound; one must not identify the radius with diameter. At epsilon=0, r is constant on connected M and direct metric scaling instead gives the sharper diam_g E<=Wr/b.

These conclusions do not give a uniform original-metric width bound if r is unbounded. They do not claim a Lipschitz constant for F, asymptotic dimension, uniform large-scale multiplicity, or equivariance. Completeness concerns h and g separately, not the conformal area metric used in stable-surface minimization.

## 3. An exact compensated hypothesis in every source dimension

Suppose, for every test phi,

    Q_4,g(phi) >= integral [b^2/r^2 + 2 Delta(log(b/r))
                           +(n-2)|dlog(b/r)|^2] phi^2.            (9)

By (2), Q_4,h>=integral psi^2 dvol_h. Section 2 proves all the global source hypotheses for h. Apply T if n=3 and S if n>=4 to obtain a continuous map to a simplicial complex of dimension <=n-2 with entire h-fibers <=C_n. Equations (5)-(8), with W=C_n, give its original-metric variable-radius control.

No separate local maps are glued in this argument. A single global complete h is supplied to the source's entire countable assembly, so its compatibility and continuity at infinity are retained. In dimension three T supplies a locally finite graph. For higher n use precisely S's stated simplicial-complex conclusion; no local-finiteness or properness upgrade is assumed here. Section 7 explains the extra construction-level information required for such an upgrade.

## 4. Paying the conformal error with an explicit energy reserve

A simpler sufficient assumption is: for some 0<alpha<=4 and kappa>0,

    Q_(4-alpha),g(phi) >= kappa integral r^-2 phi^2,               (10)
    b^2 := kappa - (n-2+4/alpha) epsilon^2 >0.

The coefficient-zero case alpha=4 is interpreted literally as a scalar form inequality. From (2), integration by parts, and completing a square,

    Q_4,h(psi)
      = Q_(4-alpha),g(phi)
        + integral [alpha |dphi|^2+4phi<df,dphi>-(n-2)|df|^2phi^2]
      >= integral [kappa r^-2-(n-2+4/alpha)|df|^2]phi^2
      >= b^2 integral r^-2 phi^2 = integral psi^2 dvol_h.          (11)

The completed square is alpha|dphi+(2/alpha)phi df|^2. This proof uses the stated reserve, not an unstated Sobolev inequality. It is a routine conformal/Young/source composition. It is nevertheless fully global and gives all the conclusions and metric comparisons of Section 3 with that b.

A pointwise assumption Scal_g>=kappa/r^2 is covered by alpha=4. Thus the already-compatible pointwise variable-scale route costs (n-1)epsilon^2, rather than an unspecified cutoff error. This is not offered as a new result.

## 5. Local spectral assumptions: the exact IMS payment

Suppose a locally finite smooth family chi_i satisfies sum_i chi_i^2=1, each chi_i supported in an open U_i, and each local test eta in C_c^infinity(U_i) satisfies

    Q_(4-alpha),g(eta) >= integral v_i eta^2,

where 0<=alpha<4 (alpha=4 follows directly as a potential statement). Locally finite sums on compact test supports justify the identity

    sum_i Q_(4-alpha),g(chi_i phi)
       = Q_(4-alpha),g(phi)+(4-alpha) integral sum_i|dchi_i|^2 phi^2.

Consequently, if pointwise

    sum_i v_i chi_i^2 - (4-alpha)sum_i|dchi_i|^2 >= kappa/r^2,    (12)

the global bound (10) follows. With alpha>0 and its positive b, Sections 2 and 4 now complete the entire local-to-global-to-width composition. Supports must be contained in U_i; for a compactly supported phi, chi_i phi must be a compact local test. Local finiteness and the support assumption guarantee this.

The data in (12) must be supplied, including scale-dependent overlap/gradient bounds. Scalar curvature does not imply them. No claim is made that arbitrary local spectral lower bounds provide a suitable partition or pay their own IMS costs. With alpha=0, this still gives a critical Q_4 bound, and Section 6 handles that case in dimension three through the additional original coefficient construction.

## 6. Stronger three-dimensional reduction using the original i14 construction

The eligible original mathematical sections of i14 already contain the full coefficient extension 4<=a<6, with width 500s_a/sqrt(lambda), where s_a^2=(8-a)/(2(6-a)). That original scope is not nominated, altered, renamed, or assigned a new grade here. Nor is an administrative status or another agent's result used as a premise. The following reproduces the actual mathematical interfaces that permit its composition with T.

Start with Q_a,g>=lambda. Rescale to lambda=1 and obtain a positive smooth solution/supersolution by compact Dirichlet exhaustion, normalized at a basepoint, Harnack, and local elliptic estimates. On a closed manifold use the positive lowest eigenfunction. Set T=-(a/2)log u, beta=4/a, gamma=2-1/beta, c_beta=(3beta-2)/(2beta-1), s=c_beta^-1/2. Then beta>2/3, gamma>1/2, and D_beta(g,T)>=1.

On a two-sided stable weighted mu-surface H-nu(T)=mu, let p=log w for a positive Jacobi eigenfunction on a closed sheet or on a relatively compact interior domain, and U=T|Sigma-p. The Gauss/Jacobi cancellation gives the EXACT nonnegative remainders

    D_gamma(k,U) >= D_beta(g,T)+c_beta mu^2+2nu(mu)
       +(1/beta)|dp+(beta-1)d_Sigma T|^2
       +|B_0|^2+(beta-1/2)[nu(T)+mu/(2beta-1)]^2.                 (13)

For a surface with D_gamma(k,U)>=c, the index form of an exp(-2U)k-geodesic, after the test substitution phi=exp(-U/2)psi, is bounded above by

    integral [2gamma/(2gamma-1) |psi'|^2 - (c/2)psi^2].

The sine test gives original k-length <=2pi sqrt(gamma/((2gamma-1)c))=2pi s/sqrt(c). Compact conformal minimization supplies this estimate; on an open sheet it is applied between nested compact domains to obtain the local exit estimate. There is no assertion of global conformal completeness. Integrating the surface inequality gives positive Euler characteristic, hence sphere or projective plane.

T's maximal nonseparating cuts are then locally finite: sheets meeting a fixed compact set remain in its compact 2pi s-neighborhood, and independent mod-two classes give a finite bound there. Its compact antisymmetric-current detection, local area retraction at a cut boundary, and the local exit estimate furnish the same separating pieces with detection radius 10s. Finite fundamental groups of the cut boundaries are retained.

For the weighted double, write m=log slice-volume - T, so m'(0)=0. At the seam the possibly discontinuous quadratic part is

    -|A|^2+(1-beta)(tr A)^2
      = -|A_0|^2-(beta-1/2)(tr A)^2,

which is concave. The source's even smoothing averages A and -A; all other required derivatives converge as in its actual collar argument. Jensen therefore preserves the lower bound up to an arbitrarily small compact-collar error. Choose each collar separately to retain D_beta>=1/2 and g/4<=h<=4g. Local finiteness supplies smooth global data without uniform derivative bounds.

On the reflected distance band choose A in (ell-90s,ell-89s), B in (ell-20s,ell-19s), |d rho|<=2, and mu=s cot(pi(rho-A)/(B-A)). Then

    2|dmu| <= (4pi s/(B-A))(1+mu^2/s^2)
             <= (1/4)(1+c_beta mu^2).

Equation (13) gives surface lower bound 1/4, hence interface diameter 4pi s. The compact constrained minimization/reflection, boundary barriers and regularity are exactly T's operations, with these rescaled widths and this pressure. The separating-interface tree anchors each connected slab to one such interface. The original h-slab diameter is <220s and projected g-diameter <440s.

Finally T's compactly supported partition and anchored collar homotopies give the continuous map to a locally finite graph. The paired collar diameter is L_s=2pi s+2s. Old-simplex entire fibers have diameter <=440s+2L_s<500s, because every collar addition is anchored in the same cover set. New path interiors belong to one pair of collars, so their entire fibers have diameter <=L_s. All changes are locally finite and descend through the proper cut quotient. Scaling back gives the coefficient-extension interface with 500s_a/sqrt(lambda). This is a reconstruction of the old compatible operation, not a new candidate.

Now assume ONLY the critical global hypothesis in dimension three,

    Q_4,g(phi) >= kappa integral r^-2 phi^2,   0<=epsilon<sqrt(kappa). (14)

For 4<a<6, identity (1) and integration by parts give

    Q_a,h(psi) >= integral [kappa r^-2-c(a)|df|^2]phi^2,
    c(a)=A_a^2/(a-4)-B_a=(8-a)/(a-4).

Indeed the available square is (a-4)|dphi-A_a phi df/(a-4)|^2. Thus choose b^2=kappa-c(a)epsilon^2>0 and use the reconstructed coefficient interface on the complete h=b^2r^-2g. It supplies W=500s_a. The geometric conversion depends only on W/b.

Let q=(a-4)/(8-a), so 0<q<1, c=1/q, s_a^2=1/(1-q). If epsilon>0, the optimal choice for this composition is q=epsilon/sqrt(kappa), equivalently

    a = 4(sqrt(kappa)+2epsilon)/(sqrt(kappa)+epsilon),
    s_a/b = 1/(sqrt(kappa)-epsilon).                             (15)

This follows either by differentiating q/[(1-q)(kappa q-epsilon^2)] or by completing the elementary square in its denominator. The fiber conclusion in ORIGINAL g is, for every x in a nonempty fiber E,

    E subset closed_B_g(x,
        r(x)[exp(500epsilon/(sqrt(kappa)-epsilon))-1]/epsilon).   (16)

The corresponding diameter is at most twice the same expression with inf_E r. At epsilon=0, use T directly on the constant rescaling to obtain diam E<=500r/sqrt(kappa), with no limiting factor 2. The graph is locally finite, continuity and infinity behavior are inherited from the completed construction. No Lipschitz or equivariant conclusion is attached.

The condition epsilon<sqrt(kappa) is a sufficient condition for this composition. Its failure is NOT proved to obstruct a variable-scale width map, and its threshold is not asserted sharp. In particular the Euclidean radial example below cautions against interpreting algebraic failure as geometric obstruction.

## 7. Topology of the higher-dimensional target and optional construction-level refinement

A continuous uniformly cobounded map alone does not imply properness or local finiteness of its target. Here is the exact additional data that would suffice, and how it relates to the paid reconstruction.

Suppose reconstruction coordinates t_i:M->[0,1] have locally finite compact supports, every x has some t_i(x)=1, and at most n-2 coordinates strictly between 0 and 1. On each compact set only finitely many coordinates occur. The standard staircase triangulation of the finite cube with the fixed 1-coordinates therefore defines a continuous map into the usual weak/polyhedral realization of the finite-subset complex (vertices are nonempty finite subsets of indices; edges and simplices are chains of inclusions). Its image lies in dimension <=n-2.

If a realized simplex is met in its relative interior, every index appearing in any of its vertices has t_i>0 somewhere at that point, hence that point lies in supp(t_i). Fix a vertex S of the subcomplex generated by all such realized simplices and an i in S. Every realized simplex containing S is witnessed in the compact set supp(t_i). Only finitely many labels have supports meeting that compact set. Hence only finitely many such simplices contain S, and their faces add only finitely many further simplices incident to S. This proves local finiteness of the generated subcomplex.

For properness, a compact subset of that locally finite target meets only finitely many simplices. For each such simplex and each point of its relative interior in the image, at least one index is positive. Its inverse image lies in a finite union of the associated compact supports; including faces gives a finite union for the whole compact target set. The inverse image is closed by continuity and hence compact. This proves properness GIVEN the coordinate data.

P's reconstruction uses fixed original outer balls, small-displacement proper identifications and locally stationary compact supports; S invokes that interface. This explains why compact coordinate supports are the relevant data to inspect, and why merely renaming the existence map is not a new operation. To avoid silently upgrading a headline theorem, Sections 3-5 assert only its stated target conclusion. This paragraph is an explicit elementary reconstruction criterion, not a separate nominee or claim of Lipschitz control.

## 8. Higher-dimensional coefficient descent: the calculation and the unpaid compatibility

The smooth hypersurface calculation in (13) has a useful general form. In an m-dimensional ambient manifold, m>=3, let beta>(m-1)/m and gamma=2-1/beta. With the same weighted Jacobi construction, Gauss and |B|^2=|B_0|^2+H^2/(m-1) give

    D_gamma(k,U) >= D_beta(g,T)+c_m(beta)mu^2+2nu(mu)
      +(1/beta)|dp+(beta-1)d_Sigma T|^2
      +|B_0|^2+[beta-(m-2)/(m-1)]
          [nu(T)+mu/((m-1)beta-(m-2))]^2,
    c_m(beta)=[m beta-(m-1)]/[(m-1)beta-(m-2)] >0.               (17)

The tangential and normal completions are algebraic and exact. Moreover gamma>(m-2)/(m-1), and iteration beta->2-1/beta gives

    beta_j = [(j+1)beta-j]/[j beta-(j-1)].                       (18)

The formal smooth descent reaches a surface coefficient >1/2 exactly when the initial beta>(n-1)/n, or a=4/beta<4n/(n-1). This is a feasibility calculation, not a codimension-two theorem.

The complete paid S/P construction is stronger than a bare smooth descent: its preprocessing, pressure, singular walls, compact shield fronts, seams, whole-packet coercivity, bounded resolvent and product compatibility must all work together. They do at their supplied coefficients. Equation (17) does not supply these operations for beta<1.

In particular, let h_+=h+du^2, l=(1+|du|_h^2)^-1/2, T_+=T-log l-u be S's quadratic-reserve graph update. The EXACT difference for beta<1 is

    D_beta(h_+,T_+)-D_beta(h,T)
      = [D_1(h_+,T_+)-D_1(h,T)]
           +(1-beta)(|dT_+|_h+^2-|dT|_h^2).                    (19)

Along a level of u its extra term is

    (1-beta)[-2<d_tan T,d_tan log l>+|d_tan log l|^2].           (20)

S's actual graph proof retains a nonnegative multiple of |d_tan log|du||^2, but gives no independent positive |d_tan T|^2 reserve that would immediately absorb (20). Its weighted-discrepancy equation controls the normal derivative using H, pressure and the angle derivative; that is not a bound on the tangential term. Thus simply replacing D_1 by D_beta in S's reserve proposition has not been justified here. Neither this calculation nor a failed estimate proves that another integrated method is impossible.

Likewise P's regularization uses its actual 3.99 form coefficient and 399 warps, matching-trace boundary contributions, the stated Hardy bounds (.78 relative to the reserve), and compatible bounded resolvents on whole packets. A generalized formal smooth descent does not authorize changing those constants or replacing the scalar reconstruction by a D_beta construction. These are concrete extra obligations, not defects in the stipulated source proof.

## 9. Sanity examples and the precise stopping point

On Euclidean R^n, n>=3, the Hardy identity gives

    4 integral |dphi|^2 >= (n-2)^2 integral |x|^-2 phi^2
                         >= (n-2)^2 integral (1+|x|^2)^-1 phi^2.

For completeness, integrate div(x/|x|^2)=(n-2)/|x|^2 in the square
integral |dphi+(n-2)x phi/(2|x|^2)|^2; remove the origin by a small cutoff and pass to the limit. The cutoff error tends to zero for n>2. Thus a positive variable lower function does not imply a uniform positive spectral constant. In dimension three a uniform graph-width bound is impossible for Euclidean space: on arbitrarily large spheres a graph map lifts to a tree, whose compact image is contained in a finite subtree (compact subsets of the usual graph CW realization lie in finite subcomplexes). Embed that finite subtree in the plane. Borsuk--Ulam then gives an antipodal pair with the same image, of Euclidean distance twice the sphere radius. The source is not applicable with a fixed lambda.

There is nevertheless a perfectly good VARIABLE-scale map x->|x| into the half-line: its whole fibers are spheres of diameter 2|x|. With r=sqrt(1+|x|^2), epsilon=1 and kappa=1 in n=3, (15) is unavailable while this radial map works. Therefore the sufficient threshold of Section 6 is not a claimed sharp obstruction.

The round stops PREFREEZE: the exact compensated and energy-reserve compositions are complete, and the stronger three-dimensional critical-form composition has been carried through the original coefficient operation and all metric conversions. These are existing-operation consequences. The potentially nonroutine higher-dimensional critical interface remains unresolved: one needs a compatible way to normalize a slowly varying critical form without the reserve in (10), or a new full D_beta preprocessing/regularization/assembly beyond (17). No exact new viable full-scope theorem has been frozen, and no exhaustion of the family or literature is claimed.

For precision, the unclosed exploratory question (NOT a frozen theorem) is whether, for every n>=4, some dimension-only eta_n,A_n>0 give a continuous map to an at-most-(n-2)-dimensional simplicial complex with

    E subset B_g(x,A_n r(x)/sqrt(kappa)) for every x in each entire fiber E,

under Q_4,g>=kappa r^-2 on C_c^infinity(M), complete connected smooth boundaryless g, smooth positive r, and |dr|_g<=eta_n sqrt(kappa), allowing r to be unbounded. No Lipschitz, proper or equivariant map is built by this question. Equations (9)-(12) close explicit stronger hypotheses, and (14)-(16) close the three-dimensional case by an existing composition. When r has a finite global upper bound, the source immediately gives a uniform width bound C_n sup(r)/sqrt(kappa); that paid consequence is not the pointwise scale control sought here. A bounded ratio sup(r)/inf(r) also yields a ratio-dependent pointwise scale bound by the same elementary implication. The unresolved issue concerns dimension-only control without that global ratio or the stated differential/form reserves.
