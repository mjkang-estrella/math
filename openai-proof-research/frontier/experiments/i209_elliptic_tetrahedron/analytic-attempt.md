# I209 analytic record: a tetrahedral lower bound and a failed elliptic upper route

2026-10-12. **PROVED NOMINATION:** every finite cylinder cover of a regular tetrahedron T satisfies

    sum_i |B_i| >= (sqrt(15)/9) A_min(T).

The constant is optimal among lower certificates obtained from nonnegative polynomial densities of degree at most two supported on T using one uniform line-integral bound, as defined in Section 5. It is NOT claimed to be the covering infimum. These are one connected contribution, not two independent findings. Neither acceptance gate is claimed passed. The improved upper-cover objective remains unresolved. No research code, numerical experiment, parameter scan, test suite, child agent, snapshot, seal or historical replay was used.

## 1. Scope and I203 dependency check

All pinned corpus theorems and lower operations are accepted. The supplied I203 result remains a candidate with pending independent validation. Its live review files are not read.

Put J=[[0,-1],[1,0]], D=1+k^2, B=[[k,2k],[-1,0]], G=[[0,2k/D],[-1,2k^2/D]]. Then det B=2k, det G=2k/D and B^{-1}=[[0,-1],[1/(2k),1/2]]. The columns of (I+tJ)G are (t,-1) and (2k(1-tk)/D,2k(k+t)/D). Multiplying those columns gives

    B^{-1}(I+tJ)G = [[1,-2k(t+k)/D],[(t-k)/(2k),1]].

The off-diagonal product is (k^2-t^2)/D, between zero and k^2/D<1 for every |t|<=k. The actual accepted source lemma b:lattice, read in its linear-coverings.tex, requires only 0<=alpha beta<1. It has no separate smallness condition on alpha or beta. Thus this application is valid, including t=+-k and all intermediate heights. This check is not an independent acceptance of the complete I203 nonlinear theorem. Route A uses that theorem conditionally. The nominated Route B uses neither I203 nor any elliptic-cover theorem.

## 2. Definitions and elementary tetrahedral data

A cylinder is C=B+R u, where |u|=1 and B is a Lebesgue-measurable subset of u-perp of finite planar area. Bases need not be convex, connected, compact or bounded. A finite cover means T is contained in the union of finitely many such C. Costs count multiplicity.

Use an edge-two regular tetrahedron centered at zero with vertices v_1,...,v_4. Its Gram matrix is

    v_i.v_i=3/2,       v_i.v_j=-1/2 (i!=j),       sum_i v_i=0.

For barycentric coordinates lambda_i>=0, sum lambda_i=1,

    x=sum_i lambda_i v_i,       |x|^2=2 sum_i lambda_i^2-1/2.       (1)

Its volume is 2sqrt(2)/3 and A_min(T)=sqrt(2). These are the same accepted normalizations as the source companions. For completeness, the model

    {(x,y,sqrt(2)t):0<=t<=1, |x|<=1-t, |y|<=t}

has volume sqrt(2) integral_0^1 4t(1-t)dt=2sqrt(2)/3. The entering-face projection formula is A(u)=3 vol(T) sum_(d_i>0)d_i, where d_i=D_u lambda_i. Since u=sum d_i v_i, sum d_i=0, the positive and negative parts express u as s times the difference of two points of T. Its diameter is 2, so s>=1/2. Equality occurs in an edge direction. This proves the shadow minimum sqrt(2), without adding a new finding for this paid calculation.

Uniform volume on a tetrahedron has lambda_i marginal density 3(1-t)^2 on [0,1], by slicing parallel to a face. Hence

    mean(lambda_i^2)=3 integral_0^1 t^2(1-t)^2dt=1/10,
    mean_T |x|^2=2(4/10)-1/2=3/10.                              (2)

## 3. A sharp quadratic chord bound

For a>=3/2, let f_a(x)=(a-|x|^2)1_T(x), and put

    M(a)=sup over all affine lines ell of integral_ell f_a ds.

The density is nonnegative, bounded and integrable. For any nondegenerate chord with endpoints p,q in T, let l=|p-q| and m=(p+q)/2. Direct integration along the segment gives

    integral_[p,q] (a-|x|^2)ds = l(a-|m|^2-l^2/12).               (3)

This identity does NOT assume that m is the foot of the perpendicular from the origin.

Write the barycentric endpoint vectors as r=(r_i), s=(s_i), and their midpoint vector as w=(r+s)/2. The Gram matrix gives

    l^2=2 sum_i(r_i-s_i)^2,
    |m|^2=2 sum_i w_i^2-1/2.

Because r_i s_i>=0,

    sum_i w_i^2 >= (1/4) sum_i(r_i-s_i)^2,
    |m|^2 >= l^2/4-1/2.                                       (4)

Also |m|^2>=0 and 0<=l<=2. Therefore (3) is bounded by

    l(a-l^2/12)              for 0<=l<=sqrt(2),
    l(a+1/2-l^2/3)          for sqrt(2)<=l<=2.                  (5)

The first expression is increasing on its interval when a>=3/2. The derivative of the second is a+1/2-l^2. Consequently

    M(a) = (2/3)(a+1/2)^(3/2)     if 3/2<=a<=7/2,
    M(a) = 2(a-5/6)               if a>=7/2.                    (6)

To verify equality, rather than only an upper estimate, take barycentric endpoints

    r=(z,1-z,0,0),        s=(0,0,z,1-z),        1/2<=z<=1.

Their supports are disjoint, so (4) is an equality. Their squared distance is

    l^2=4[z^2+(1-z)^2]=2+8(z-1/2)^2,

which ranges over [2,4]. Thus every maximizing length in the second part of (5) is realized by a chord between opposite edges. The segment is the entire intersection of its line with T: extending past either endpoint makes a previously zero barycentric coordinate negative. Points and empty intersections have integral zero. This proves (6) for all lines, including boundary lines.

At a=19/10 the maximizing length is sqrt(12/5); for example take z=(1+1/sqrt(5))/2. Equations (2) and (6) give

    integral_T f_(19/10) dx =16sqrt(2)/15,
    M(19/10)=16sqrt(15)/25.                                    (7)

These constants are exact symbolic evaluations.

## 4. The lower bound for actual finite covers

For any cylinder C=B+R u, Tonelli in the orthogonal decomposition R^3=u-perp+R u gives

    integral_C f_(19/10) dx
      = integral_B [integral_R f_(19/10)(b+su)ds]db
      <= (16sqrt(15)/25)|B|.                                   (8)

All affine lines are covered by (6); there is no restriction on the cylinder direction. This works for every measurable base and for translates, which are absorbed into B. If C_1,...,C_N cover T, nonnegativity implies

    16sqrt(2)/15 = integral_T f_(19/10)
       <= sum_i integral_(C_i) f_(19/10)
       <= (16sqrt(15)/25) sum_i |B_i|.

Thus

    sum_i |B_i| >= sqrt(30)/9 = (sqrt(15)/9) A_min(T).           (9)

Similarities give the same ratio for every regular tetrahedron of positive edge length. For edge length e the absolute bound is e^2 sqrt(30)/36. No finite approximation, limit interchange, inverse map, wall condition, endpoint removal, smoothness of bases or existence of a minimizing cover is used. In particular, (9) is a statement about actual finite covers, not a local integral proposed as an upper cover. Allowing an uncovered volume-null subset would not invalidate the argument, though the task asks for closed-body coverage.

The primary universal lower bound is A_min/3. Our constant exceeds it because sqrt(15)>3. This is a substantial exact lower-bound change for the regular tetrahedron, not a tuning of the old angular construction. The accepted angular upper bound remains in force. Nothing here asserts equality in (9), attainment of a covering infimum, or sharpness of the classical 1/3 in a wider class.

## 5. Exact optimality within quadratic density certificates

For any nonzero real polynomial q of degree at most two, nonnegative on T, define

    Cert(q)= integral_T q dx / [A_min(T) sup_ell integral_(ell intersect T) q ds].

The denominator is positive and finite. Averaging q over the finite orthogonal symmetry group of T preserves its integral and nonnegativity. For each line the average's integral is the average of q's integrals over the transformed lines; hence its supremum cannot increase. It suffices to optimize invariant quadratics.

In coordinates with vertices (1,1,1)/sqrt(2), (1,-1,-1)/sqrt(2), (-1,1,-1)/sqrt(2), (-1,-1,1)/sqrt(2), the symmetries include coordinate permutations and changing the signs of any two coordinates. Invariance kills all linear and mixed quadratic terms and makes the three diagonal coefficients equal. Thus the average is alpha+beta|x|^2.

If beta>=0, positivity at the center gives alpha>=0. An edge chord has length 2 and mean |x|^2=5/6. Consequently

    Cert(q) <= (alpha+(3/10)beta)/(3alpha+(5/2)beta) <=1/3.       (10)

If beta<0, multiplication by a positive scalar reduces to q=a-|x|^2 with a>=3/2, since the maximum radius occurs at the vertices. By (2) and (6),

    Cert(f_a)=(a-3/10)/(a+1/2)^(3/2)    (3/2<=a<=7/2),
    Cert(f_a)=(a-3/10)/(3a-5/2)        (a>=7/2).                (11)

The first derivative has the sign of 19/20-a/2. The second derivative has numerator -8/5. Thus the unique maximizing a in this radial family is 19/10, and its value is

    (8/5)/(12/5)^(3/2)=sqrt(15)/9.                             (12)

Equations (10)-(12), with symmetrization, prove

    sup {Cert(q): deg q<=2, q>=0 on T, q not identically 0}
       =sqrt(15)/9.

This optimality is only for the specified certificate class. It does not rule out better nonquadratic densities or a non-density argument. Uniqueness of nonsymmetric maximizers is not asserted. The certificate optimization explains and supports (9); it is not nominated separately.

## 6. Route A: exact mixed elliptic/hyperbolic wall geometry

This independent upper-cover route was developed first and retained after failure. Write a=1/2, h=sqrt(2), and use labels (b,r) in the wedge |b|<=r. For a radial stream function

    psi=(r^2-b^2)f(r),        V=(psi_r,-psi_b),

one has div V=0 and P=Q on b=r, P=-Q on b=-r. Every straight map p->p+s tau V(p) therefore maps each wall into itself as a set whenever its wall factor stays positive. Wall tangency alone does not prove global coverage or surjectivity.

For f=r^(m-1),

    V=r^m((m+1)-(m-1)(b/r)^2, 2b/r),
    det DV=-2m r^(2m-2)[(m+1)+(m-1)(b/r)^2].                  (13)

For m>=0 this is the paid hyperbolic/nilpotent radial family, up to normalization (the source parameter is p=m+1). For -1<m<0, there is elliptic expansion in a central angular sector. Its unweighted positive determinant integral diverges at the apex, with radial power integral r^(2m-1)dr, while the slope-square integral stays finite for m>-1. The improved multiplier does not remove this difference.

To make the failure quantitative, take the distinct mixed field m=-1/2, normalized to Q(b,a)=b:

    P(b,r)=(a/4)(r/a)^(-1/2)[1+3(b/r)^2],
    Q(b,r)=a(r/a)^(-1/2)(b/r),
    det DV=a^3[1-3(b/r)^2]/(8r^3).                             (14)

The central sector |b/r|<1/sqrt(3) is elliptic and the walls are hyperbolic. This is not the paid m=0 angular field. At b=+-r, det DV=-a^3/(4r^3); hence the I203 condition for axial half-length L=1 forces

    tau^2 a^3/(4d^3)<1                                        (15)

on a cutoff r>=d. The stronger sufficient inverse condition tau d^(-3/2)->0 is natural. It shows why removing the cutoff without a bound is invalid.

### Wall factors and actual coverage for fixed cutoff

Fix 0<d<a, then make tau>0 small. The identities

    Q+-P = ((r+-b)/2)(r/a)^(-3/2)[(3/2)b/r +-1/2]

give the signed wall factorizations. On a ball of radius R/4 about any target (B,R) with R>=2d, V=O_d(1), DV=O_d(1). The map p->(B,R)-s tau V(p), |s|<=1, is a contraction into the ball for small tau. Its inverse has r>=d, and the two wall factors 1+O(tau d^(-3/2)) are positive. Therefore the inverse label lies in the closed wedge, including its walls.

Let

    P_a(b)=a/4+3b^2/(4a),       Dcap(b)=b^2 P_a(b),
    D_(tau,d)={d<=r<=2, |b|<=r,
               r<=a+tau^2 Dcap(b)+q},      q=tau^(5/2).

Use two families

    (y,t)=(b,r)+tau x V(b,r),       |x|<=1,
    (x,1-t)=(b,r)-tau y V(b,r),     |y|<=1.

Outside t<2d and 1-t<2d the inverse argument applies to both. If both cap conditions failed, the inverse heights r_-,r_+ would exceed a. Initially each is a+O_d(tau), and Q(b,a)=b cancels their first-order shifts, improving this to a+O_d(tau^2). Substitution then gives

    r_-+r_+=1+tau^2[x^2 P_a(y)+y^2 P_a(x)]+O_d(tau^3).

But

    Dcap(x)+Dcap(y)-x^2P_a(y)-y^2P_a(x)
       =(3/(4a))(x^2-y^2)^2 >=0.

Replacing target coordinates by inverse labels in Dcap changes the right side by O_d(tau). Thus simultaneous failure would imply 2q<=O_d(tau^3), contrary to tau^3=o(q). The cap argument is closed and includes equality cases. The artificial r<=2 cutoff is not reached when tau is small. Two original-axis triangular cylinders with 0<=t<=2d and 0<=1-t<=2d cover the removed ends, at normalized cost 4d^2 each.

For each fixed d,tau satisfying these conditions, D_(tau,d) is compact and V is smooth on a neighborhood. Its trace is zero and (15) ensures det D(tau V)>-1. CONDITIONAL ON I203's nonlinear theorem, each ruled family therefore has an actual finite cover with compact parallelogram perpendicular bases, cost at most

    h integral_(D_(tau,d)) [1+tau^2(det DV)_+]
                /sqrt(1+tau^2(P^2+2Q^2)) db dr + e.

Both finite errors can be chosen to sum to any epsilon>0 after fixing d,tau. The coordinate swap and physical height reflection for the second family are isometries. Together with the two explicit triangular tip cylinders this is a cover of the entire closed tetrahedron. This conditional existence is not a claimed improvement.

### All terms of the proposed cost

For H_d={d<=r<=a, |b|<=r}, elementary integration gives

    integral_-a^a Dcap(b)db=7a^4/15,
    (1/2) integral_(H_d)(P^2+2Q^2)dbdr
        =(29a^3/30)(a-d),
    integral_(H_d)(det DV)_+ dbdr
        =a^3/(6sqrt(3))(1/d-1/a).                              (16)

For the last identity integrate 1-3z^2 over |z|<=1/sqrt(3); its integral is 4/(3sqrt(3)). This is precisely the coefficient-one elliptic penalty, not the older coefficient two. The physical area Jacobian is h/sqrt(1+tau^2(P^2+2Q^2)); omitting the 2 in the Q term would be wrong.

At fixed d the integral and cap expansion, plus both tip cylinders, give the guaranteed normalized bound

    1/2+6d^2+2tau^2 F_d+4a tau^(5/2)+O_d(tau^4)+epsilon/h,

where

    F_d=-a^4/2+(29a^3/30)d
                  +a^3/(6sqrt(3))(1/d-1/a).                   (17)

The cap-strip corner areas are O_d(tau^4); multiplying the order-tau^2 integrand correction by the order-tau^2 cap area is also O_d(tau^4). The deletion at r<d and its two replacement tips produce the displayed 6d^2. No limit uniform as d->0 is asserted.

In fact this coefficient is positive for EVERY 0<d<=a, not just near the apex. Set z=d/a and c=2/(3sqrt(3)); since a=1/2,

    F_d/a^4=-1/2+(29/30)z+c(1/z-1).

The exact inequalities 3/8<c<2/5 and AM-GM give

    (29/30)z+c/z >=2sqrt(29/80)>6/5,
    F_d/a^4 >6/5-1/2-2/5=3/10.                               (18)

Thus this new mixed field, with its actual wall/cap/tip accounting, yields no saving in the displayed fixed-cutoff expansion even under the improved multiplier. Taking d->0 makes the penalty coefficient diverge; no favorable d-dependent Taylor limit is claimed. Nor can the ordinary tips be o(tau^2) while maintaining the small-derivative schedule: they would need d=o(tau), inconsistent with tau d^(-3/2)->0. These are failures of this certificate/construction, not lower bounds against all possible uses of elliptic fields.

For a separate elementary rigidity check, an affine trace-free field tangent to both wedge walls must be V=b_0(r,b). Indeed write V=(A b+B r+C,D b-A r+E) and impose P=Q at b=r and P=-Q at b=-r. This gives A=C=E=0, B=D. Its determinant is -b_0^2. Thus a single affine field preserving both walls cannot be elliptic; using I203 substantially on this geometry requires nonlinear fields or patch transitions.

## 7. Literature, novelty boundary and handoff

The mass/maximum-line-integral principle in (8) is classical. Bezdek–Litvak's primary Theorem 3.1 proves 1/3 directionwise for all three-dimensional convex bodies and 1 for ellipsoids; its ellipsoid argument uses a nonnegative density with constant line integrals. Their section/projection inequality is also paid. The new proposed content is the explicit tetrahedral chord calculation (4)-(6), the absolute finite-cover constant sqrt(15)/9, and its exact optimality within all nonnegative quadratic polynomial certificates. None of the four source companions states this lower certificate in the actual sections read. They provide upper covers and their normalization, and their strict half-bound results remain accepted.

The lower bound concerns absolute area relative to the minimum projection of a REGULAR tetrahedron. It is not an improved directionwise-normalized bound for arbitrary tetrahedra: an arbitrary affine map changes different cylinder base areas by different factors. No inference of that type is made. The upper interval endpoint remains the accepted angular finite construction; it is not nominated again. In particular this record does not answer the original elliptic upper-cover challenge positively.

The exact statements and proof are new-to-project deductions. No worldwide priority or comprehensive best-current-tetrahedron-lower-bound claim is inferred from searches. The primary comparison and its scope are recorded in literature.md. Both the proof gate and the contribution/novelty gate remain with the parent. The sharper quadratic certificate is one supporting part of the same lower-bound nomination, not a second finding.
