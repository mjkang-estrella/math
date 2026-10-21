# Author proof of the frozen selected-current shell theorem

This is discovery-stage author proof, not a downstream manuscript or a review gate. The exact scope is FROZEN-STATEMENT.md (SHA256 53f35f024803059dd77264ffc0f00d0c20209a3768e61551e8285eccaf7d5b38). Its bytes remain unchanged. All source operations below are stipulated at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. No upstream truth audit is performed.

## 1. Source interfaces and notation

In this proof S means the pinned manuscript **Sharp integral fillings in CAT(0) spaces**, with canonical main path recorded in private/source/authentication.json. Labels are its actual TeX labels. We use the full sharp theorem in cycle dimensions n and n-1, always with n>=3. Thus the lowest sharp filling used is for integral 2-cycles. Set c_j=1/((j+1)((j+1)omega_(j+1))^(1/j)). The source provides compactly supported integral fillings of every compactly supported integral j-cycle in any proper CAT(0) space, with mass at most c_j M^(1+1/j), for j>=2. Integer multiplicity is unrestricted.

The other operative inputs from S are:

* Section 02, `thm:current-background`: integral compactness on a compact CAT(0) space, attainment and weak continuity of minimum filling mass on mass-bounded sequences of cycles, the linear cone bound, and current restriction, slicing, homotopy and pushforward calculus. Filling continuity is the actual Wenger theorem, not an inference from weak lower semicontinuity alone.
* Section 02, `prop:chart-mass`: disjoint rectifiable charts with Euclidean metric differential G, mass density |theta| sqrt(det G), integer |theta|>=1, intrinsic scalar derivatives and |Du|<=Lip(u). All gradients in this proof are these chart covectors, not derivatives on an assumed smooth support.
* Sections 03–07: the normalized-comparison radial, small-set, gradient-closure, compactness, subthreshold-minimizer and chord operations. Section 3 below states exactly how they are applied when the comparison coefficient is c_n/H rather than the source's coefficient c>c_n. No false claim that our cycle is the source's positive maximizer is made.

Closed balls in X are compact and convex. Fix one such ball Y containing support T. Its nearest-point projection is 1-Lipschitz and fixes Y. Pushing any compact filling onto Y cannot increase mass or change a boundary supported in Y. Consequently the filling infimum for cycles in Y equals the one in X. The infimum in Y is attained, and its minimizer has compact support. Write V for this common value for cycles in Y. It is symmetric and subadditive; in particular |V(B)-V(C)|<=V(B-C). Every cycle in Y has V(B)<=L_Y M(B) for a finite cone constant L_Y. These facts hold also after a constant metric rescaling. We use the sharp degree-n filling bound V(B)<=c M(B)^q, with s,c,q as frozen.

The barycenter of a probability measure supported in Y lies in Y: projection onto Y lowers its squared-distance functional. The CAT(0) squared-distance inequality gives existence by compactness and uniqueness by strict convexity along a segment between two distinct minimizers. Thus the barycenter considered in Y below is the unique barycenter in X.

## 2. Selection with a multiplicative comparison inequality

Suppose first delta>0; lambda=sqrt(delta)>0. Minimize over all integral n-cycles B in Y the functional

    Phi(B)=c M(B)^q - V(B) + lambda V(B-T).

The sharp theorem makes its first two terms nonnegative. A minimizing sequence has bounded mass because

    Phi(B)>=c M(B)^q-L_Y M(B),

which tends to infinity as M(B) tends to infinity. Integral compactness gives a weakly convergent subsequence to an integral cycle A in Y. The source's filling continuity gives V(B_j)->V(A) and V(B_j-T)->V(A-T); the latter sequence is also mass-bounded and consists of cycles. Mass lower semicontinuity and continuity of t^q show that Phi(A)<=liminf Phi(B_j). Thus a minimizer exists.

Since Phi(A)<=Phi(T)=delta L_T, both nonnegative terms give

    V(A-T)<=lambda L_T,
    0<=c M(A)^q-V(A)<=delta L_T.                       (2.1)

The triangle inequality and V(T)=(1-delta)L_T give

    V(A)>=(1-delta-lambda)L_T>0,
    c M(A)^q<=V(A)+delta L_T<=V(T)+lambda L_T+delta L_T
             =(1+lambda)L_T.                          (2.2)

Here 1-lambda-lambda^2>0 because lambda<=1/4. Therefore A is nonzero and (2.2) gives precisely the frozen mass bounds. An attaining filling of A-T in Y supplies Q with the required boundary and mass.

For every integral n-cycle B in Y, minimizing comparison gives

    c(M(A)^q-M(B)^q)
       <=V(A)-V(B)+lambda(V(B-T)-V(A-T))
       <=(1+lambda)V(A-B).                             (2.3)

If delta=0, take A=T and Q=0. Because c M(A)^q-V(A)=0 is the global minimum of the nonnegative deficit functional, the same calculation with lambda=0 proves (2.3). The mass bounds then hold with equality. This also handles the zero-deficit case without taking a limit of selected cycles.

Put R_A=(M(A)/s)^(1/n) and rho=R_A/H, H=1+lambda. For Sections 3–7 replace d by d/rho. Masses in dimensions n and n+1 scale by rho^(-n) and rho^(-n-1), respectively. Both sides of (2.3) have degree n+1, so the normalized comparison is

    c_eff(m^q-M(B)^q)<=V(A-B),
    c_eff=c/H,   m=M(A)=s H^n,
    c_eff q m^(1/n)=1/n.                              (2.4)

All measures, distances and radii until Section 8 refer to this normalized metric. Notice m<=mbar. No geometric homothety of X is needed: we rescale its metric and the associated current mass convention.

## 3. Radial and critical inequalities at this comparison coefficient

We justify the operative use of S rather than silently importing its original contradictory assumption m<s. Consider any nonzero cycle satisfying (2.4) on compact CAT(0) Y.

The proof of S `prop:radial` uses the radial pushforward B_h=(F_h)#A and the homotopy current D_h for F(t,x)=[y,x]_(1-t g(x)), with g nonnegative Lipschitz. Its chart determinant estimates are

    M(B_h)<=m-h int(ng+r Dr.Dg) dmu+O(h^2),
    M(D_h)<=h int r g sqrt(1-|Dr|^2) dmu+o(h),
    boundary D_h=B_h-A.

The error estimates concern fixed y,g and are valid on compact Y. Applying (2.4), dividing by h and using c_eff q m^(1/n)=1/n gives

    int(ng+r Dr.Dg) dmu
       <=n int r g sqrt(1-|Dr|^2) dmu.                (3.1)

The sign of c_eff-c_n does not occur in this derivation. This is the full normalized radial inequality for every center y in Y. The chart calculus requires no normality of individual chart restrictions.

Next S `prop:small-set` fills the boundary of a superlevel restriction U of mass a by R of mass d using the sharp (n-1)-cycle theorem. Comparing B=A-U+R in (2.4), and using any available coarse degree-n filling coefficient K_n, gives, when d<a<=m/2,

    (2^(-1/n)/n)(a-d)<=K_n(2a)^q.

Hence d>=a-O(a^(1+1/n)), with a finite constant independent of the level function. Since d<=(P/(n omega_n^(1/n)))^(n/(n-1)), small restrictions have the same almost-Euclidean perimeter coefficient as in S. This argument needs m>0 and (2.4), not m<s. S `lem:intrinsic-coarea` then applies to the cycle identity and its charts; it permits arbitrary, including atomic or singular, distributions of level values.

The rest of Section 04 operates on exactly this small-set inequality: its generalized-inverse rearrangement and sharp radial Euclidean inequality, followed by truncation, yield for every eta>0

    (S_*-eta)||u||_p^2<=4/(n-2) E(u)+C_eta||u||_2^2,
    p=2n/(n-2),  S_*=n s^(2/n),                       (3.2)

on Lipschitz functions, with C_eta independent of u. The Section 05 proof of `prop:sobolev-space` closes the chart gradient using boundary A=0; `prop:compact-embedding` uses that closure, small-set estimate and compactness of Y. Neither proof uses m<s. Thus its Hilbert space H embeds compactly into L2, continuously into Lp, satisfies (3.2), and has the stated chain rules and extension of (3.1) to nonnegative H tests.

We claim the sharper inequality

    Q(u):=4/(n-2) E(u)+n||u||_2^2 >= S_*||u||_p^2.   (3.3)

Indeed let Lambda be the infimum of Q over ||u||_p=1. Inequality (3.2) implies Lambda>0. Assume Lambda<S_* for a contradiction. The proof of S `prop:minimizer` after its constant-test line now applies: a minimizing sequence is weakly compact in H and strongly compact in L2; the critical splitting gives, with t=int|u|^p,

    Lambda>=Lambda t^(2/p)+S_*(1-t)^(2/p).

For t<1 the right side is strictly greater than Lambda; thus t=1, and the infimum is attained. Rescaling a nonnegative minimizer produces v with

    W=int v^p dmu=(Lambda/n)^(n/2)<s,
    Q(v)=nW,
    4/(n-2) int Dv.Dpsi+n int v psi=n int v^(p-1)psi. (3.4)

The only use of m<s in the source minimizer proof (lines 424–428) was to obtain Lambda<S_* from the constant test. Here that strict bound is the contradiction assumption, not an asserted consequence of our mass.

S `lem:powers` and `lem:composites` use (3.2), (3.4), finite mass and compact Y; they give the moments and admissible chord tests without boundedness or strict positivity of v. Section 06 `prop:chord-transform` and `lem:chord-density` consequently yield

    L_y<=2(W/s)^(2/n)<2

for almost every center relative to v^p mu/W, where L_y is its conformally weighted chord moment. Section 07 `lem:opposite-average`, using (3.1), the Euler equation and CAT(0) variance, gives the average of these same L_y at least 2. This contradiction proves (3.3). All these are operative source proofs with their needed premises supplied. In particular we have not asserted that v=1 is a minimizer when H>1, or that the mass m is below s.

## 4. Connectedness and dimension-only density and diameter

Let K=support A, a nonempty compact set. If it is disconnected, K has a partition into two nonempty disjoint compact relatively open subsets K1,K2. Their distance is positive. A Lipschitz cutoff constant 0 and 1 on their neighborhoods has no mass in its intervening levels. Slicing at a regular such level yields a mass-additive split A=C+D into integral cycles supported in the two sets. Each has positive mass by the definition of support. Relabel so a=M(D)<=m/2. Comparing B=C in (2.3) and using the sharp filling theorem gives

    m^q-(m-a)^q<=H a^q.

But with z=m/a>=2 the left side divided by a^q is z^q-(z-1)^q, an increasing function of z, hence at least 2^q-1. The frozen lambda_n is strictly less than 2^q-2, so H<2^q-1, a contradiction. Thus K is connected.

Fix x in K, let a(r)=mu(B(x,r)), and use open balls throughout. For almost every r the restriction U=A restricted to B(x,r) is integral and P=M(boundary U)<=a'(r), by the intrinsic coarea bound for the 1-Lipschitz distance. Fill boundary U inside Y by an integral n-current R, with

    d=M(R)<=c_(n-1) P^(n/(n-1)).

If a<=m/2 and d<=a/2, comparison with A-U+R, followed by sharp degree-n filling, yields

    2^(-1/n) a/(2n)
       <=c_eff(m^q-(m-a+d)^q)
       <=V(U-R)<=c(a+d)^q<=c(3a/2)^q.

The first inequality uses (2.4) and the derivative lower bound on [m/2,m]. Rearranging forces

    a>=Acrit:=s(n+1)^n/(n^n 3^(n+1)).                 (4.1)

The frozen a0=Acrit/4 is less than m/2: indeed ((n+1)/n)^n<3 and n>=3 imply a0/s<1/(4*3^n)<1/2, whereas m>=s. Therefore whenever 0<a(r)<=a0, (4.1) forbids d<=a/2. At almost every such radius,

    a'(r)>=(a(r)/(2c_(n-1)))^((n-1)/n).              (4.2)

At a support center a(r)>0 for every r>0. On compact positive-radius intervals before a reaches a0, the monotone function a^(1/n) has nonnegative singular derivative and absolutely continuous derivative at least 1/[n(2c_(n-1))^((n-1)/n)]. Integrating from t to r and then letting t decrease to zero proves

    a(r)>=min{a0,b r^n},   b=omega_n/2^(n-1).         (4.3)

If a reaches a0 first, monotonicity gives the same bound thereafter. This reasoning does not assume that a is absolutely continuous. Limits from smaller radii give the open-ball bound also at exceptional radii. In particular every open r0-ball centered on K has mass at least a0.

If the diameter of K is d_K, compactness gives a pair realizing it. From one member x, the continuous distance function on connected K has image the whole interval [0,d_K]. Choose points at distance levels 0,3r0,6r0,...,3Nr0, where N=floor(d_K/(3r0)). Their open r0-balls are disjoint by the triangle inequality. Thus (N+1)a0<=m<=mbar. Since d_K<3r0(N+1) except for an immaterial endpoint where the same weak bound holds, the deliberately loose frozen bound

    diam K<=D=3r0(mbar/a0+1)                          (4.4)

follows. This removes dependence on the diameter of the original support or the initially chosen compact ball.

## 5. The finite-defect chord operation

Put nu=mu/m. For a fixed y in K let r=d(y,.), L=int r^2 dnu, k=(n-2)/2 and

    J(a)=int (1+a r^2)^(-n) dnu,
    G(a)=k int_0^1 J(au)u^(k-1) du,    a>=0.

On K, 0<=r<=D. All these functions have the differentiability needed below by bounded convergence. Completing the square in (3.1) gives, for every nonnegative Lipschitz g,

    int(ng|Dr|^2+r Dr.Dg)dmu <=(n/4)int r^2 g dmu.   (5.1)

Indeed 1-r sqrt(1-|Dr|^2)-|Dr|^2+r^2/4 is the square (sqrt(1-|Dr|^2)-r/2)^2. Take

    w(t)=(1+a t^2)^(-k),
    f(t)=int_0^1 z^(n-1) w'(zt)^2 dz.

These are smooth bounded profiles with bounded first derivatives, f>=0, and nf+tf'=w'^2. The test g=f(r) in (5.1) yields

    int w'(r)^2 |Dr|^2 dmu <=(n/4)int r^2 f(r)dmu.

Consequently, writing beta=1/(n-2),

    Q(w(r))<=n int (w(r)^2+beta r^2 f(r))dmu =n m G(a).  (5.2)

The scalar identity on the right is exactly

    (1+z)^(-(n-2))
      +k z^2 int_0^1 u^(n/2)(1+zu)^(-n)du
        =k int_0^1 u^(k-1)(1+zu)^(-n)du,

obtained by integrating the derivative of u^k/(1+zu)^(n-2). Its integrability at zero holds also for n=3. This is the unweighted specialization of the actual source chord calculation; no quotient-minimizing property of the constant function is invoked.

Apply (3.3) to w(r). Since int w(r)^p dmu=m J(a) and m=s H^n, (5.2) gives

    H^(-2) J(a)^((n-2)/n)<=G(a).                      (5.3)

Set C=H^(2n/(n-2)) and h(a)=G(a)^(-1/k). Changing variables in G gives a G'=k(J-G), so for a>0,

    a h'=h-J G^(-n/(n-2))>=h-C,
    J<=C h^(-n/2).                                   (5.4)

At H>1, the quantity (h-C)/a has negative infinite initial limit. Replacing C by 1 or simply integrating from zero would be invalid. We retain C and start at a positive parameter.

For t>=0 the third derivative of (1+t)^(-n) is negative, hence its quadratic Taylor polynomial is an upper bound:

    (1+t)^(-n)<=1-nt+n(n+1)t^2/2.

Integrating first in nu and then in u gives

    G(a)<=1-(n-2)La+[n(n+1)k/(2(k+2))]a^2 int r^4 dnu.

Convexity of z^(-1/k) at z=1 implies h>=1+(1-G)/k. As int r^4<=D^4, we obtain for every a>=0

    h(a)>=1+2La-gamma D^4 a^2,
    gamma=n(n+1)/(n+2).                              (5.5)

From (5.4), (h(a)-C)/a is nondecreasing on (0,infinity). Suppose first C>1 and choose

    a_* = sqrt((C-1)/gamma)/D^2 >0.

Equations (5.4)–(5.5) imply for all a>=a_*

    h(a)>=C+a K_*,
    K_*=2L-2D^2 sqrt(gamma(C-1)).                     (5.6)

If K_*<=0, then L<=D^2 sqrt(gamma(C-1)), already stronger than the desired bound below. If K_*>0, (5.4)–(5.6) imply

    limsup_(a->infinity) a^(n/2)J(a)<=C K_*^(-n/2).   (5.7)

At mu-almost every center, integer Euclidean tangent density gives

    liminf_(a->infinity) a^(n/2)J(a)>=s/(2^n m).       (5.8)

For clarity, this is S `lem:chord-density` with v=1: choose a density point in a disjoint current chart, rescale coordinates by a^(-1/2), use its Euclidean metric differential and Lebesgue value of |theta|sqrt(det G), and apply Fatou on each fixed coordinate ball. Letting that ball increase to all of R^n gives |theta|int_Rn(1+|z|^2)^(-n)dz/m=|theta|s/(2^n m), at least (5.8). There is no uniform tangent radius, bounded multiplicity, or interchange of limits in the center required.

Combining (5.7) and (5.8) bounds

    K_*<=(2^n C m/s)^(2/n)=4 C^(2/n)H^2=4C.

Together with the K_*<=0 case, this proves for almost every center

    L<=2C+D^2 sqrt(gamma(C-1)).                       (5.9)

If C=1, (5.4) and (5.5), integrated from arbitrary a_*>0 and then a_* down to zero, give h(a)>=1+2La. Equations (5.4),(5.8) then give L<=2 because m=s. Thus (5.9) remains valid at lambda=0. The kernel d(x,y)^2 is bounded Borel, so this almost-everywhere bound can be averaged without any jointly measurable choice of chart derivatives.

## 6. Barycenter and squared radial deviation

Let o be the barycenter of nu. The CAT(0) variance inequality says

    int d(y,x)^2 dnu(x)>=int d(o,x)^2 dnu(x)+d(o,y)^2.

One direct proof is to use the CAT(0) squared-distance inequality along the segment from o to y in the minimizing property at o, divide by the segment parameter, and let the parameter decrease to zero. Averaging in y yields

    2 int d(o,x)^2 dnu(x)<=int L_y dnu(y).

By (5.9), the right side is at most 2C+D^2 sqrt(gamma(C-1)). Apply (3.1) with center o and constant g=1. Dividing by nm gives

    1<=int d(o,x)sqrt(1-|D d(o,.)|^2)dnu(x)
      <=int d(o,x)dnu(x).

Therefore

    int(d(o,x)-1)^2dnu
       <=int d(o,x)^2dnu-1
       <=C-1+(D^2/2)sqrt(gamma(C-1))
       =epsilon_n(lambda).                           (6.1)

The center o need not belong to K; it belongs to Y, which is exactly the domain of the all-center radial inequality.

## 7. Every-point concentration

Fix x in K and put t=|d(o,x)-1|. If t=0 there is nothing to prove. The function z->d(o,z)-1 is 1-Lipschitz. On the open ball B(x,min(t/2,r0)), its absolute value is at least t/2. The density estimate (4.3) and (6.1) therefore imply

    epsilon_n(lambda) m
       >=(t^2/4)b min(t/2,r0)^n.                     (7.1)

If t/2<=r0, (7.1) gives t<=2(m epsilon_n/b)^(1/(n+2)). If t/2>=r0, it gives t<=2(m epsilon_n/(b r0^n))^(1/2). Since m<=mbar, the frozen Psi_n bounds both cases. The argument works at every support point, including points outside the almost-everywhere chart set. When epsilon_n=0, (7.1) forces t=0 everywhere on K.

## 8. Restoring scale and completing the statement

Return from d/rho to d. The probability measure nu=||A||/M(A) and its barycenter are unchanged under metric rescaling. Equations (4.4),(6.1),(7.1) become precisely the frozen diameter, mean-square and every-point annulus estimates. The mass and Q estimates were proved in the original metric in Section 2. Taking the appropriate power of the mass ratio in (2.2) gives

    (1-lambda-lambda^2)^(1/(n+1))<=R_A/R_T
       <=(1+lambda)^(1/(n+1)),

and division by H gives the stated radius interval.

For fixed n, C-1 tends to zero linearly with lambda, so epsilon_n tends to zero and Psi_n tends to zero. The displayed formulas in the frozen statement, not an unspecified asymptotic constant, are the theorem. They also show a dimension-dependent upper bound of order delta^(1/(4(n+2))) as delta decreases to zero. The proof includes arbitrary integer multiplicities and unrestricted ambient dimension throughout. Properness and compact support were used to obtain a compact convex Y and actual integral minimizers; no completeness/properness hypothesis has been dropped.

This completes the author derivation at the frozen scope, subject to independent review. Neither exact equality classification nor quantitative closeness to a flat ball is inferred from the annulus conclusion.
