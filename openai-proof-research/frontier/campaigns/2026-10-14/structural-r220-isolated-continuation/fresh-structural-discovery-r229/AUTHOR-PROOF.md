# Author proof of the entire frozen r229 statement

This proof addresses exactly `STATEMENT.md`, SHA256 `febac8d7844dbc09a741b31c52bfc05da9d2b9d116ea1bdda42ed19aad0455e9`. It neither modifies that scope nor assigns a review grade. The sole solution under discussion is the normalized Source353 radial solution specified there. All source assertions and operative proofs at the pin are stipulated true.

## 1. Paid inputs and conventions

The dimension-ten source establishes smooth radial F,P on R^9, positive F,P and H=D²_xF, the displayed radial equations, and the smooth entire affine-maximal function u(x,t)=sqrt(F²+t²). Its reduction proposition gives, in the original affine coordinates,

    D²u=(F/u)H+(F²/u³)(dt−(t/F)dF)²,
    det D²u=F^11 u^(−12) det H,
    det H=F P^(−12/11).

In tau=log r the source's autonomous system is X'=V(X), where

    A'=A(1+B−A),
    B'=B(9+A+(12/11)BD−9B),
    D'=(11−D)A−8D+BD(1−D/11).

A prime on X or another function of tau in §§2–4 means d/dtau; primes on F,P,y mean d/dr. The source proves that X remains in the box [0,9/2]×[0,7/2]×[0,33/7], and that A,B,D are positive for r>0. No assertion about convergence to the corner or an asymptotic rate is imported.

The rigidity companion, including its geometric rescalings, cap identity, tube coercivity, logarithmic cell bounds and final rescaling, has been read but is not used to infer anything beyond its dimension range. The new proof below is specific to graph dimension ten. We do not suspend a lower-dimensional solution or change the determinant exponent.

## 2. Monotone convergence to the critical corner

Smoothness of the radial profiles at the origin gives even Taylor expansions. The local source values yield

    F=1+r²/2+a r⁴+O(r⁶),    P=1−11r²/18+O(r⁴).

In the first radial equation, (y/r)^8 y'=1+44a r²+O(r⁴), whereas FP^(−12/11)=1+7r²/6+O(r⁴). Thus a=7/264. Consequently

    A=r²+O(r⁴),
    B=1+(7/33)r²+O(r⁴),
    D=(11/9)r²+O(r⁴).

The remainders may be differentiated once with r d/dr, by the smooth even expansions. Therefore all three components of X'=V(X) are strictly positive for sufficiently small r>0.

Inside the source box the off-diagonal entries of DV are nonnegative:

    V1,B=A;  V2,A=B;  V2,D=(12/11)B²;
    V3,A=11−D;  V3,B=D(1−D/11),

and the remaining off-diagonal entry is zero. Along the solution, h=X' satisfies the linear equation h'=DV(X)h. On every finite time interval choose M so large that DV(X)+MI is entrywise nonnegative. The integral equation for e^(M tau)h, or its convergent Picard iteration, preserves the nonnegative cone; each component stays strictly positive if it was initially positive. This is an elementary finite-interval comparison, with no global uniform ellipticity assumption. Hence every coordinate of X is strictly increasing for all r>0.

The box gives a limit X∞. Continuity of V implies V(X∞)=0: otherwise a component of X' would converge to a nonzero value, contradicting convergence. We have A∞>0, B∞>1, D∞>0. The first two equilibrium equations imply

    B∞=A∞−1,
    D∞=11(4A∞−9)/(6(A∞−1)).

Substitution into the third equation gives exactly

    0=55(2A∞−9)²/[36(A∞−1)].

Therefore X∞=X*=(9/2,7/2,33/7). Strict increase ensures every coordinate is strictly below its corresponding limiting value at every finite r. In particular the deficit z=X*−X is componentwise positive and tends to zero.

## 3. Stable projection and the neutral quadratic drift

Taylor expansion of the polynomial vector field gives

    z'=Jz−Q2(z)+O(|z|³),

where Q2 is the homogeneous quadratic part of V(X*+z), and

    J=[−9/2,     9/2,       0;
        7/2,   −27/2,  147/11;
       44/7,  132/49,     −12].

Its characteristic polynomial is lambda(lambda+15)². Define

    v=(1,1,110/147),
    ell=(308,132,147)/550.

Direct multiplication gives Jv=0, ell J=0, ell v=1. These identities and J(J+15I)²=0 were also checked using exact rational arithmetic. Set q=ell z and w=z−qv. The positivity of ell and z gives q>0 and |z|≤Cq. Also q→0, and w lies in E=ker ell. The projection onto span(v) is Pi=v ell. On E, J has only the eigenvalue −15, with at most a size-two Jordan block. More explicitly, (J+15I)² vanishes on E, so

    ||exp(sJ)|E|| ≤ C(1+s)exp(−15s),  s≥0.

Write N(z)=z'−Jz. Then N(z)=O(q²), whence |q'|=|ell N(z)|≤Cq². This estimate gives the two slow-variation facts needed below. First, (1/q)'≤C, so for sufficiently large tau,

    q(tau)≥c/(1+tau).

Second, for any epsilon>0 and sufficiently large T, |q'|/q≤epsilon on [T,infinity). Thus for T≤s≤tau,

    q(s)≤exp(epsilon(tau−s))q(tau).

The projected integral equation is

    w(tau)=exp((tau−T)J)w(T)
       + integral_T^tau exp((tau−s)J)(I−Pi)N(z(s)) ds.

Taking epsilon<1, its integral is bounded by

    C q(tau)² integral_0^infinity (1+h)exp(−(15−2epsilon)h) dh.

The initial term is exponentially small and is O(q(tau)²) by the polynomial lower bound for q. Hence

    z=qv+O(q²).

This step is essential: convergence to a nonhyperbolic equilibrium alone would not justify integrating a power-law asymptotic, and we have not assumed a center-manifold theorem or an integrable linearized family.

The exact quadratic coefficients along v are

    Q2(v)=(0,20/7,−2530/3087),
    ell Q2(v)=7/15.

For example the second component is 1−9+(12/11)(33/7+7·110/147)=20/7. The third is −(6/7)(110/147)−(7/22)(110/147)²=−2530/3087. Substituting z=qv+O(q²) into q'=ell N(z) therefore yields

    q'=−a q²+O(q³),     a=7/15.

Let h=1/q. Then h'=a+O(q). Since q→0, integration first gives h/tau→a, hence q=O(1/tau). Integrating again gives h=a tau+O(log tau), and inversion gives

    q=15/(7tau)+O(log tau/tau²).

Together with w=O(q²), this proves the complete vector asymptotic in part 1 of the frozen statement. In particular the actual trajectory has a nonzero neutral component: positivity supplied q>0 and its polynomial lower bound. There is no unproved assumption that a stable trajectory misses a faster-decaying submanifold.

## 4. Integrating the asymptotics and matching constants

The first coordinate gives

    d(log F)/dtau=9/2−15/(7tau)+O(log tau/tau²).

Since the error is integrable at infinity, its integral has a finite real limit and its remaining tail is O(log tau/tau). Exponentiation gives a strictly positive cF and

    F=cF r^(9/2)(log r)^(−15/7)[1+O(log log r/log r)].

Similarly C=BD has expansion

    C=33/2−[(33/7)+(7/2)(110/147)]q+O(q²)
     =33/2−(22/3)q+O(q²).

Thus

    d(log P)/dtau=−33/2+110/(7tau)+O(log tau/tau²),

and a positive cP exists with the asserted expansion for P. The constants are attached to the fixed normalized source solution; there is no claimed free parameter in them.

The identities y=AF/r and y'=ABF/r² turn the first radial equation into the exact identity

    A^9 B F^8 P^(12/11)=r^18.

Inserting the limits of A,B and the preceding asymptotics cancels both the r powers and the log powers and gives

    (9/2)^9(7/2)cF^8 cP^(12/11)=1.

All conclusions of part 1, including the constant constraint, are now proved.

## 5. The global metric and its radial coordinate

Put zeta=t/F and v=asinh zeta. Since F is smooth and positive on all R^9, (x,v)↦(x,F(x)sinh v) is a global smooth diffeomorphism, including x=0. Pulling back the source quadratic tensor, rather than recomputing a coordinate Hessian, gives

    D²u=(1+zeta²)^(−1/2)H
          +F(1+zeta²)^(−3/2)d zeta².

The original affine-coordinate determinant is

    det D²u=P^(−12/11)(1+zeta²)^(−6).

Its −1/12 power is P^(1/11)(1+zeta²)^(1/2). Since d zeta=cosh(v)dv, the metric is exactly

    g=P^(1/11)[H+F dv²].

The factor P^(1/11) and the determinant exponent are specific to dimension ten. This change is a parametrization of the same hypersurface, not a claim that a non-affine coordinate change preserves a graph PDE.

We next prove the global lower bound Q=FP^(1/11)≥1 in the frozen statement. Let E=A−C/11. Near zero E=(8/9)r²+O(r⁴)>0. The source equations in A,B,C include

    C'=C(1+C−8B)+11AB.

At any point where E=0, therefore C=11A, direct subtraction gives

    E'=A(8B−12A).

The source box D=C/B≤33/7 implies, at such a point, B≥7A/3. Hence E'≥(20/3)A²>0. There cannot be a first zero reached from positive E: its derivative there would be nonpositive. Thus E>0 for every r>0. Since d(log Q)/dtau=E and Q(0)=1, Q is strictly increasing.

For r>0 the radial Hessian is H=F''dr²+rF' g_S8. Define

    rho(r)=integral_0^r sqrt(P^(1/11)F'') ds.

It is strictly increasing and is r+O(r³) near zero. Set K=cF cP^(1/11)>0. Part 1 gives

    Q=K r³(log r)^(−5/7)[1+O(log log r/log r)].

Moreover

    d rho/dr=sqrt(ABQ)/r,
    d(sqrt Q)/dr=E sqrt Q/(2r),
    AB→63/4,   E→3.

The first formula and the displayed growth of Q show rho→infinity (for instance the integrand is bounded below by c r^(2/5) for large r). Both rho and sqrt Q tend to infinity, and their derivative quotient tends to

    2sqrt(63/4)/3=sqrt 7.

The elementary l'Hopital rule, or integration of upper and lower derivative bounds, therefore gives rho/sqrt Q→sqrt 7. In this coordinate

    g=d rho²+phi(rho)² g_S8+psi(rho)²dv²,
    phi²=QA,   psi²=Q.

It follows that phi²/rho²→9/14 and psi²/rho²→1/7. Smoothness across the axis follows from the already smooth positive tensor in the Cartesian (x,v) coordinates, so no polar-coordinate singularity is being admitted.

For completeness, rho and v each change by at most the length of any path: the first follows from the radial metric coefficient, and the second from psi²=Q≥1. These statements remain valid across the axis by absolute continuity of the radial coordinate along piecewise smooth paths. A g-Cauchy sequence therefore has bounded rho and bounded v. Since rho is a proper increasing function of |x|, the sequence lies in a compact subset of the Cartesian coordinate space. Smooth positivity of g gives local metric equivalence to the Euclidean metric on a neighborhood of that compact set. A convergent Cartesian subsequence converges in g, and the g-Cauchy property then gives convergence of the entire sequence. Thus g is complete. This property was already obtained in eligible original history by a simpler source-bound argument and is not counted as distinct work here.

The Euclidean graph metric is also complete because the graph is entire and smooth: its distances dominate base Euclidean distances, and a base Cauchy limit has a smooth graph lift. This observation is not used to infer affine completeness. Nor is the Hessian metric interchangeable with either metric: on x=0 its t-direction coefficient is (1+t²)^(−3/2), whose square root has finite integral to infinity. Pointwise Hessian positivity supplies no global uniform lower bound.

## 6. Global ball geometry and the exact volume coefficient

Let d be the distance from p0, which is (x,v)=(0,0). For a point with coordinates (rho,omega,v), travel first on the central axis and then along a radial meridian at fixed v. Since psi(0)=1 and the radial coefficient is one, this path has length |v|+rho. Thus

    d≤|v|+rho.

The reverse asymptotic bound must allow paths taking advantage of the cheap axis direction. Fix K0>0 and any path from p0 to the point, of length L. Split its length into L_in on rho<K0 and L_out on rho≥K0. Since psi is increasing and at least one,

    |v|≤L_in+L_out/psi(K0)≤L_in+L/psi(K0).

The total variation of (rho−K0)_+ along the path is at least (rho_final−K0)_+. Therefore L_out≥(rho_final−K0)_+. Combining these inequalities gives

    L(1+1/psi(K0))≥|v|+rho_final−K0.

Taking the infimum over paths proves the same inequality with L=d; it does not assume a minimizing path stays in a prescribed compact set. Define

    D(T)={(rho,omega,v): rho+|v|<T}.

We have, for every R,K0>0,

    D(R) ⊂ B_g(p0,R)
         ⊂ D(R(1+1/psi(K0))+K0).

Choose K0=sqrt R. The already proved psi(K0)/K0→1/sqrt 7 gives an outer parameter R+O(sqrt R). This comparison is global in omega and v, including v of order R. Merely using a tensor limit at large rho with bounded v would not give this result.

Away from the measure-zero axis the volume element is

    dVol_g=phi(rho)^8 psi(rho) d rho d omega dv.

Write W(rho)=phi^8 psi. The metric limits imply

    W(rho)~kappa rho^9,
    kappa=(9/14)^4/sqrt 7.

Near zero W is smooth in the appropriate polar sense and is O(rho^8). In particular it is locally integrable; globally W≤C(1+rho^9). Direct integration gives

    Vol_g(D(T))=2|S^8| integral_0^T (T−rho)W(rho) d rho.

Scaling rho=T s and using either dominated convergence or two-sided asymptotic bounds outside a fixed compact interval gives

    lim_(T→infinity) Vol_g(D(T))/T^11
      =2|S^8| kappa integral_0^1 (1−s)s^9 ds
      =|S^8| kappa/55.

The ball inclusions with outer parameter R+O(sqrt R) give the same limit for B_g(p0,R). Finally, for any fixed p, put d0=d_g(p,p0). For R>d0 the triangle inequality yields

    B_g(p0,R−d0) ⊂ B_g(p,R) ⊂ B_g(p0,R+d0).

Dividing volumes by R^11 proves the same coefficient at p. This completes the entire frozen statement.

## 7. Exact scope and strongest-reduction comparison

The graph's existence, smoothness, nonlinear equation and positivity are the paid Source353 construction, not an approximate or weak replacement. The companion's dimension-three-through-nine rigidity is also paid and is not extended by contrapositive. The eligible r28 original metric factorization and completeness bound were executed and explicitly retained as paid. The Trudinger–Wang 2000 singular power calculation and its weak variational verification, and the 2026 preprint's radial variational barrier/global continuation, supply the closest actual primary construction comparisons. Their operations explain the power corner and smooth existence; the present argument begins beyond these operations.

The proposed distinct content is the critical neutral drift for the fixed smooth radial orbit, its forced logarithmic renormalization, and the global metric-ball comparison converting the warped density to the exact R^11 volume law. The nonzero neutral component and the global path comparison are proved above, rather than supplied as conditional bridges. No parameter freedom, affine inequivalence classification, uniform perturbative theorem, higher-dimensional suspension, entire Legendre dual, or proper metric tangent cone is claimed.

All constants and the numeric volume coefficient use the fixed normalization F(0)=P(0)=1. Under a fixed ambient affine transformation with linear part L, the pulled-back Berwald–Blaschke metric scales by |det L|^(2/12); this follows by normalizing the conormal in the affine-area formula. Thus completeness and the growth exponent survive, whereas this numerical coefficient would scale by |det L|^(−1/12). This is explanatory covariance, not an additional nominated family.

The proof is an author submission only. Independent adversarial correctness review and separate primary-literature contribution review remain for the parent. The scoped search/read record does not establish worldwide novelty or exhaustive project-history clearance. There is no formal proof claim: the pinned Lean comparator itself ends in `sorry`, and no downstream formalization was undertaken.
