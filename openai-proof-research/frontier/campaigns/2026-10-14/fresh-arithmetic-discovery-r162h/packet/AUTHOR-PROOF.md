# Author proof: quantitative rigidity of critical inverse-square affine laws

This develops exactly FROZEN-STATEMENT.md, SHA256 1d2799dba1c5bffca37724769974e56dc0e6c6ec2ac0196a01c3f15039ce6133. It is an author-proof submission for independent review, with no self-assigned correctness, contribution, acceptance or count. All constants below are finite; none is asserted sharp. The frozen estimate uses squared compact C^m error and exponent 1/4.

## 1. Inputs, notation, and their actual scope

Use H, K, Q, T and P as in the frozen statement. Write eta=1-beta and k=(beta+3)/4, so 0<=eta<=1/4 and 15/16<=k<=1. Expectations are under P. For z=x+iy set

    q_F(z)=-iy F''(z)/F'(z)=a_F(z)+i b_F(z),
    G_(k,F)(z)=F(z)-iy F'(z)/k,
    J_(k,F)(z)=det D G_(k,F)(z)/|F'(z)|^2.

The stipulated Brennan source, build/sections/01-preliminaries.tex, Lemma lem:compact-class, supplies compactness of K and uniform bounds for all F and Q derivatives on each source compact. This includes positive lower bounds for |F'| and |Q| on each source compact, by nonvanishing and compactness. It also supplies |F|>=1/16 on S0={|m(z)|>=1/2}, m(z)=(z-i)/(z+i). These statements do not require bounded image or a regular boundary.

Its affine identities are

    T_w(T_z F)=T_(z dot w) F,  z dot w=x+yw,
    Q_(T_z F)(w)=Q_F(z dot w)/Q_F(z),
    q_(T_z F)(w)=q_F(z dot w).

We assume the exact covariance of P. We do NOT invoke the source's eigenmeasure construction outside its rho>2 hypothesis. In particular, an arbitrary law of finite-scale extremizers is not a permitted replacement for P.

The source's local differential calculations are valid for every k>0:

    k^2 J_k=k(k-1)+(2k-1)a+|q|^2.                 (1)

Differentiating E|Q_F(x+iy)|^2=y^(-beta), with uniform local derivative bounds justifying differentiation, gives

    E a_F(i)=-beta/2,
    E b_F(i)=0,
    E|q_F(i)|^2=beta(beta+1)/4.

Hence, using 2k-1=(beta+1)/2,

    E J_k(i)=(k-1)/k=-eta/(beta+3).              (2)

J_k(i) is bounded uniformly over K and beta in the stated interval. Both J_k and the geometric constructions below are equivariant under T.

The primary component-persistence operation used below is the oldest-component pairing of Edelsbrunner--Letscher--Zomorodian, Topological Persistence and Simplification, published 2002, Sections 2--4, especially the 0-dimensional rule on printed p.523. That finite filtration rule is classical. We give the additional smooth infinite-fiber, quantitative, Borel and affine interfaces here. The source's equal-rank pairing does not itself furnish the local gain in (8).

## 2. Escape and good targets for the assumed law

The source states its escape proposition under beta>1 because that is where it constructs its law. We verify the needed implication directly from the exact covariance hypothesis at our beta.

For fixed z!=i apply covariance to Phi(F)=|F(z#)|^(-4), where z#=(-x+i)/y. The identity (T_z F)(z#)=-F(z)Q_F(z)/y gives

    E[|F'(z)|^2 |F(z)|^(-4)]
        =y^(-beta-4) E|F(z#)|^(-4).

The affine inversion z->z# preserves S0, inverts y, and has absolute Jacobian y^(-3). Injectivity and |F|>=1/16 on S0 give

    E I(F)<=256 pi,
    I(F)=integral_(S0) y^(beta+1)|F(z)|^(-4) dA. (3)

Indeed the integral of the left side before inversion is at most integral_(|w|>=1/16)|w|^(-4)dA=256pi. Tonelli and inversion give (3).

For I(F)<infinity, submean for |1/F|^4 on B(z,y/2), for centers escaping |x|+y->infinity, gives

    [y^k/|F(z)|]^4
       <=C integral_(B(z,y/2)) (Im w)^(beta+1)|F(w)|^(-4)dA(w)->0,

since 4k=beta+3. The disks eventually avoid i and escape every bounded |x|+y region. Consequently the preimage of a compact target set, restricted to y>=epsilon, is compact, and its entire preimage has bounded height.

For a nonnegative compactly supported smooth psi on the target, set h(s)=integral_R psi(F(x+is))dx. At positive heights its support is compact. Twice integrating by parts, then changing variables conformally, gives

    h(s)=integral_(y>s) (y-s)|F'|^2 (Delta psi)(F) dA.

Thus h(s)<=Y_psi ||Delta psi||_1 uniformly in s, where Y_psi bounds the preimage heights of supp psi. In particular the total horizontal length mapped into any fixed compact target set is uniformly bounded in the height (with a map-dependent bound).

Put V_xi(z)=y^k/|F(z)-xi|, with value infinity at its possible pole. At height scale h, an omitted target of bounded modulus satisfying V_xi>=delta has, by the local quarter theorem, y|F'|<=4|F-xi|. Compact rebasing distortion therefore puts its entire horizontal witness cell of length h within C_delta h^k of xi. The horizontal-length estimate gives at most C_(F,R,delta)/h such cells. Their target disks have total area O(h^(2k-1)); the dyadic sum converges because k>=15/16>1/2. Outside an area-null target set, sup_x V_xi(x+iy)->0 as y->0. Interior targets have the same conclusion because a small target disk has compact inverse image. The preceding tail handles source infinity. Every closed positive superlevel is therefore compact for almost every target, for almost every F.

For fixed F the singular values of G_k have area zero by the plane Sard estimate proved in the source. Distinct nonsingular branches over a target have critical log-value differentials

    d_xi log V_xi(z_j(xi))(v)=Re[v/(F(z_j(xi))-xi)].

Injectivity of F makes these differentials distinct. Each tied-value locus is therefore locally a smooth curve, and a countable branch cover makes their union area-null, exactly as in the first-power companion's Lemma lem:good. Call a target good when its positive closed superlevels are compact, all its G_k preimages are regular, and their critical values are distinct. Goodness is Borel: compact-superlevel tests use rational points and a source exhaustion; singular roots and separated tied pairs are closed-projection tests on compact source boxes. Goodness is preserved under rebasing and the induced target similarity.

For a good pair (F,xi), the critical points of ell=log V_xi off its pole are the roots G_k(z)=xi. At such a point,

    V_xi(z)=k y^(k-1)|Q_F(z)|,
    Hess ell=(k/y^2)[[-(k+a), b], [b, k-1+a]],
    trace Hess ell=-k/y^2,
    det Hess ell=-k^4 J_k/y^4.                  (4)

Positive J means a saddle and negative J a finite maximum. There are finitely many critical points above each positive V level. A pole is not a G_k root and cannot be an accumulation point of the roots. Every regular positive superlevel is a finite union of Jordan disks: the source proves this by Delta ell=-k/y^2<0, excluding a hole by the minimum principle, and the compact regular level-set theorem. Its argument uses only k>0 and compactness, so applies here. No global finite number of critical points is assumed.

## 3. A component pairing with a quantitative gain

Fix a good pair. At a saddle s, the two rising local germs belong to different components U_1,U_2 of {V>V(s)}. Here is a justification of the topological facts needed. At a nondegenerate saddle, rotate coordinates so one second derivative is negative. Solve the corresponding first derivative equal to zero as v=h(u). Taylor's formula in v writes ell-ell(s)=A(u)-(v-h(u))^2 B(u,v), with B>0 and A(0)=A'(0)=0, A''(0)>0. Writing A(u)=u^2 C(u), C>0, and rescaling coordinates gives the local form U^2-V^2. Thus there are two rising germs and two descending sectors. If the rising germs belonged to the same component of the strict upper set, a simple path in that open component would join them. Join that path through s inside the two rising germs and remove loops to obtain a Jordan curve. One of the descending sectors lies in its bounded interior. The curve has ell>=ell(s), whereas that sector contains values smaller than ell(s). Its interior lies in H. The minimum principle contradicts Delta ell<0 there; a possible pole can be removed by a small circle on which ell is larger than the boundary minimum. Therefore the components are distinct.

Each U_j has a unique representative: its pole if it contains one, otherwise its largest finite maximum. Existence follows from compactness of {V>=V(s)} and a point of U_j of larger value than V(s). If the pole is absent from its closure, V attains its maximum on that compact closure and the maximum is interior. If the pole is in its closure, a whole neighborhood of the pole belongs to {V>V(s)}, so it belongs to U_j. Uniqueness follows from the absence of critical-value ties. There are finitely many possible finite maxima above V(s).

Pair s with the representative having the smaller value. Infinity is larger than every finite value, so this partner is always a finite maximum. The partner is denoted R_F(s).

This assignment is injective on saddles. To see this with the infinite-fiber issue explicit, fix any positive regular cutoff below any finite set of saddles being compared. Only finitely many critical points occur above it. On a compact strip between consecutive critical levels, the vector field grad ell/|grad ell|^2 transports level sets and components; a neighborhood of a pole stays a single component above sufficiently large levels. At a maximum, a new component is born as the level decreases. At a saddle the local form just proved joins exactly the two distinct components, and no hole is created. The representative of the union is the larger of their two representatives. Thus each smaller representative is used once at the merger where it ceases to represent a component. A representative already used cannot reappear. This is the finite oldest-component rule, and the definition for a given saddle depends only on values above its own value, so decreasing the cutoff does not change any previous assignment. Applying this to any two saddles proves injectivity on the entire countable fiber. Distinct targets have disjoint fibers, so injectivity also holds for fixed F across all saddles in the domain.

We now obtain a quantitative bound which rank ordering alone does not give. Rebase at s. Its target becomes -i/k, its base point is i, and its potential differs by a positive constant factor. On one fixed disk B(i,r0), the functions

    ell_(F,k)(w)=k log(Im w)-log|F(w)+i/k|

have uniformly bounded derivatives through order three, for all F in K and 15/16<=k<=1. Choose r0 using uniform derivative bounds so |F(w)|<=1/2 there; the denominator then stays away from zero. At a saddle at i, let j=J_k(i)>0 and let lambda be the positive Hessian eigenvalue. By (4),

    lambda(lambda+k)=k^4 j.

The uniform jet bound gives j<=Jmax and lambda<=Lambda. Therefore lambda>=c0 j with universal c0>0. Choose one universal d>0 so d Lambda<=r0/2 and the Taylor remainder for displacement t<=d lambda is at most lambda t^2/4. If e is a unit positive eigenvector, Taylor's formula gives, for 0<t<=d lambda,

    ell(i +/- t e)-ell(i)>=lambda t^2/4>0.

At t=d lambda the gain is at least d^2 lambda^3/4>=c1 j^3. These points lie on the respective rising germs, because the whole punctured segment has increased value. Both representatives thus have log-value at least ell(i)+c1 j^3. In original coordinates,

    log[V(R_F(s))/V(s)]>=c1 J_k(s)^3.           (5)

Consequently, on the saddle domain,

    c_F(s):=[V(R_F(s))/V(s)]^4
          >=1+c2 J_k(s)^3,                    (6)

for universal c2=4c1>0. This is independent of the number, locations, separation or heights of the other critical points.

## 4. Borel and covariance interfaces of this pairing

The nonzero-J root graph of G_k(F,w)=xi has countably many continuous local branches over open parameter sets, by the source's uniform local contraction argument and second countability. Activating only the first occurrence of each root gives a Borel enumeration. The pole graph, when present, has the same kind of local enumeration by the complex inverse function theorem, and has at most one point per (F,xi).

The positive eigenvector at a rooted saddle can be chosen Borel, for example by choosing a unit eigenvector with its first nonzero real coordinate positive. The corresponding one-dimensional spectral projection is continuous where the eigenvalues are distinct, as they are here. Define the two witness points with the fixed d and the positive eigenvalue from Section 3, then undo the positive affine rebasing. Their coordinates are Borel functions of the saddle data. Changing the sign convention merely exchanges the two components.

Connectivity of two Borel-varying points p,q in {V_xi>h}, for Borel positive h, is Borel. Indeed it is equivalent to existence of a polygonal path with endpoints p,q and finitely many intermediate rational-coordinate vertices contained in that open set and in H. Each segment is compact. Containment is tested by a positive margin in Im z and in

    (Im z)^k/h - |F(z)-xi|,

on all its points; uniform continuity makes this equivalent to countably many rational-parameter tests with some positive rational margin. Countably many finite polygons and margins give a Borel test. Rational intermediate vertices suffice by openness and polygonal connectivity of connected plane domains. The formula remains continuous at a pole because it has no reciprocal singularity.

For each of the two witness points, test which enumerated finite maximum roots lie in its component. Test separately whether the pole lies there. If not, select the root of largest V-value among that component's roots. Existence and uniqueness were proved above; comparison against all enumerated roots is a countable Borel condition. Then choose the representative with smaller value, treating the pole as infinity. This proves that (F,s)->R_F(s) is Borel on the good saddle domain.

The construction is intrinsic. Under t dot w=x_t+y_t w, G targets transform by (xi-F(t))/(y_t F'(t)); V transforms by the same positive scalar at every point in that fiber; source coordinates change by a positive real similarity. Critical points, signs, strict superlevel components, poles and largest representatives therefore correspond. The two local rising germs correspond as well. Hence

    R_(T_t F)(w)=t# dot R_F(t dot w),            (7)

on corresponding domains. This gives equivariance of c_F, independent of the enumeration used to establish measurability. Arbitrary coordinate tie-breaks in the enumeration have no effect on the selected geometric partner.

## 5. Transport converts the local gain to a law estimate

Put omega_F(z)=y^(beta-1)|Q_F(z)|^2 and J_+=max(J_k,0), J_-=max(-J_k,0). The source's local area formula on disjointified diffeomorphism charts gives, for every nonnegative Borel h,

    integral_H h omega J_+/- dA
      =integral_C sum_(G_k(z)=xi, +/-J_k(z)>0)
                      h(z)y^(beta-1)|Q_F(z)|^4 dA(xi).

Because 4(k-1)=beta-1, the target weight equals (V_xi(z)/k)^4. This equality of powers is retained exactly.

Good-target nullity transfers to the normalized point with its Jacobian weight. Apply the area formula to bad targets in {|x|<=1,1<=y<=2}; the integral is zero for almost every F. After expectation, covariance and equivariance identify it with

    2 log 2 E[J_+(i) 1_(bad at (F,G_k(i)))].

Thus that expectation is zero. No unweighted almost-sure goodness at the fixed target G_k(i)=-i/k is asserted.

Let D_N consist of good saddles with partner s'=x'+iy' satisfying N^(-1)<=y'/y<=N and |x'-x|<=Ny. These Borel equivariant sets increase to the good saddle domain. For B={|x|<=S,1<=y<=Y}, the included partners lie in B'={|x|<=S+NY,N^(-1)<=y<=NY}. Fiberwise injectivity and exact target weights imply

    integral_B omega J_+ c_F 1_(D_N) dA
          <=integral_(B') omega J_- dA.

Covariance converts the expected spatial density to dx dy/y. Hence

    2S log Y E[J_+(i)c_F(i)1_(D_N)]
       <=2(S+NY)(log Y+2log N) E J_-(i).

At fixed N first send S->infinity, then Y->infinity. Send N->infinity by monotone convergence. The bounded root Jacobians make the right side finite. Use the weighted bad-target identity and (6) to obtain

    E J_+(i)+c2 E[J_+(i)^4]<=E J_-(i).          (8)

Together with (2), this proves

    E[J_+(i)^4]<=eta/[c2(beta+3)],
    E|J_k(i)|=2 E J_+(i)+eta/(beta+3)
                <=C eta^(1/4).                (9)

The case eta=0 is included by these same nonnegative inequalities. There is no assumed uniform displacement cutoff or uniform compactness modulus for entire good fibers: the source's ordered box limits remove each finite N before its final exhaustion. The local gain (6) survives this exhaustion and is the quantitative addition.

## 6. An analytic determinant identity and local quadratic approximation

Write J_1 for the normalized Jacobian with parameter k=1, even when the law's beta is smaller than one. For any compact E1 subset H, compact-family bounds and (1) imply

    sup_(F,z in E1) |J_1(z)-J_k(z)|<=C_E1 eta.

Covariance applied to |J_k(i)| gives

    E[|Q_F(z)|^2 |J_k(z)|]=y^(-beta) E|J_k(i)|.

The positive uniform lower bound on |Q_F| on E1 therefore yields from (9)

    sup_(z in E1) E|J_1(z)|<=C_E1 eta^(1/4).    (10)

Let g=F', D_F=det D G_(1,F)=|F'|^2 J_1, and H_F=D_F/y. Direct calculation gives

    D_F=y^2 |g'|^2+y Im(g' conjugate(g)),
    2i H_F=(z-conjugate(z))g' conjugate(g')
                         +g' conjugate(g)-g conjugate(g').

Using Wirtinger derivatives,

    partial_z(2iH_F)=g''[(z-conjugate(z))conjugate(g')+conjugate(g)],
    partial_bar_z partial_z(2iH_F)
                 =(z-conjugate(z))|g''|^2.

Thus the exact, pointwise identity is

    Delta H_F=4y |F'''|^2.                     (11)

This requires only holomorphicity. It is not a claim that J_1 is nonnegative.

Choose any nonnegative smooth compactly supported chi in H. Integration by parts twice gives

    4 integral chi(z)y |F'''(z)|^2 dA
           =integral H_F(z) Delta chi(z) dA.

All terms are finite for each F, with uniform bounds on the fixed support. By (10), the uniform local bound for |F'|, and positive minimum y on the support,

    E integral chi y |F'''|^2 dA<=C_chi eta^(1/4). (12)

The signed right side was bounded by its absolute integral; the left side is nonnegative. Choosing chi=1 on a neighborhood of a prescribed compact, using the holomorphic submean inequality on slightly smaller disks, and using Cauchy's derivative estimates gives, for every compact E2 subset H and every j>=3,

    E sup_(z in E2)|F^(j)(z)|^2<=C_(E2,j) eta^(1/4). (13)

For clarity, a fixed disk radius within the cutoff region bounds the pointwise |F'''|^2 by a common constant times the single L2 integral in (12), uniformly over points of the smaller compact. Cauchy on a further fixed neighborhood gives higher derivatives. Thus no exchange of expectation with a supremum is assumed without a deterministic bound.

Let c(F)=F''(i) and define its quadratic Taylor polynomial

    P_c(z)=(z-i)+(c/2)(z-i)^2.

The convex hull of E union {i} is a compact subset of H. Integrating F''' along its straight segments and using F(i)=0, F'(i)=1, F''(i)=c, together with (13), gives for every compact E and every m>=0

    E [max_(0<=j<=m) sup_E |F^(j)-P_c^(j)|]^2
                        <=C_(E,m) eta^(1/4).  (14)

For j<=2 these are the elementary integral Taylor remainders; for j>=3 the polynomial derivative vanishes and (13) applies.

## 7. A universal Borel choice of the exact quadratic model

The circle C0={c:|c+i/2|=1/2} is the quadratic coefficient set. Define its Borel radial projection by

    pi(c)=-i/2+(c+i/2)/(2|c+i/2|)  if c!=-i/2,
    pi(-i/2)=0.

The distance estimate, including the center convention, is

    |c-pi(c)|=abs(|c+i/2|-1/2)
       <=2 abs(|c+i/2|^2-1/4)
       =2 abs(|c|^2+Im c)=2|J_1(i)|.           (15)

For c0 in C0 with c0!=0, a=i-1/c0 is real because Im(1/c0)=1. Direct expansion shows P_(c0)=F_a. For c0=0 it is F_infinity. The map c0->a is a homeomorphism from C0 to the one-point compactification of R. Define A(F) by this formula with c0=pi(F''(i)). It is Borel and uses none of beta, P, E or m.

Every selected model belongs to K. For finite a its derivative is (z-a)/(i-a), and equality F_a(z)=F_a(w) would imply z=w or z+w=2a; the latter is impossible for z,w in H. The affine model is immediate.

The root quantity J_1(i) is uniformly bounded. Therefore (10) at i and (15) imply

    E|c-pi(c)|^2<=C E|J_1(i)|<=C eta^(1/4).

The compact C^m distance between P_c and P_(pi(c)) is bounded by C_(E,m)|c-pi(c)| (derivatives of order >=3 are zero). Combine this with (14) and (u+v)^2<=2u^2+2v^2. This proves Claim A exactly with its squared error, exponent 1/4, universal choice A and all compact sets and finite derivative orders.

## 8. The entire critical law

At beta=1, Claim A has zero right side. A countable compact exhaustion of H shows that P is supported on {F_a:a in R union {infinity}}. This parameterization is a homeomorphism onto its compact image in K: it is continuous, including the affine limit at infinity, and injective. Let mu be the parameter law.

Rebasing gives

    T_(x+iy)F_a=F_((a-x)/y),
    |Q_(F_a)(x+iy)|^2=(1+a^2)/[(a-x)^2+y^2],  a finite.

The affine model is fixed and its Q is identically one. Testing covariance on the singleton affine model, whose preimage under any rebasing is itself, gives mu({infinity})=y^(-1)mu({infinity}). Hence that atom is zero.

For horizontal translations (y=1), apply covariance to the nonnegative parameter test phi(b)=(1+b^2)psi(b), extended Borel to K, where psi is compactly supported and nonnegative. We obtain

    integral psi(a-x)(1+a^2)dmu(a)
             =integral psi(a)(1+a^2)dmu(a).

Thus the locally finite measure sigma(da)=(1+a^2)mu(da) is translation invariant. A locally finite translation-invariant positive measure on R is c da: its values on half-open intervals depend only on their lengths, are additive and monotone, and therefore are c times length first on rationals and then on all lengths; half-open intervals determine the measure. Local finiteness also forces any atom to have zero mass. Consequently

    mu(da)=c da/(1+a^2).

Its total mass is one, so c=1/pi.

Conversely, this Cauchy parameter law satisfies the full displayed covariance. For every nonnegative Borel phi, substitute a=x+yb to get

    integral_R [(1+a^2)/((a-x)^2+y^2)]
               phi((a-x)/y) da/[pi(1+a^2)]
       =y^(-1) integral_R phi(b) db/[pi(1+b^2)].

Taking phi(a)=Phi(F_a) proves covariance for all the required tests, including infinite integrals. This proves existence and uniqueness, and Claim B.

## 9. Scope and comparison

The additional operation is the quantitatively increasing component-persistence assignment, proved Borel and affine equivariant on the full good saddle domain and compatible with the source's exact fourth-power area weights. It supplies a fourth moment of positive Jacobian from the exponent deficit. The identity (11) then converts that estimate, without dividing by a possibly vanishing pre-Schwarzian, into compact analytic rigidity. Equal-rank strictness or compactness alone does not supply this rate.

The primary oldest-component rule is not new; neither are the source's escape, target-nullity, root transfer, box exhaustion or standard local analytic estimates. The claimed theorem is their fully specified quantitative exact-law interface with the new estimates (5)--(15). Whether this constitutes a substantial contribution requires the parent's separate primary-literature review. No worldwide priority or exhaustive history assertion is made.

The theorem assumes exact inverse-square affine covariance. It does not prove it for the source's critical operator or for finite-radius optimizing maps. The rho=2 horizontal boundary term is still unpaid in that different application. No endpoint area/Lorentz/Orlicz conclusion, uniform radial bound without loss, first-power numerical gap, or arbitrary approximate-law stability is inferred. In particular i135 E_gamma/W2 and all excluded earlier scopes stay unchanged.
