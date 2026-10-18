# T117Q: negative-type metrics with large average trace-class distortion

Author: Myeongjin Kang. Author-side candidate, not independently reviewed or accepted. The full target is exactly original-scope.txt. Prose CC BY 4.0; accompanying original code MIT. Pinned source truth is stipulated. Parent mathematical assistance is explicitly credited below.

## Statement

There are an absolute c>0 and genuine finite negative-type metrics (V_j,d_j), with n_j=|V_j| tending to infinity, such that every nonexpanding map F:V_j -> S_1(H), for every complex Hilbert space H, satisfies

    E_{x,y uniform V_j} ||F(x)-F(y)||_1
      <= C (log log n_j)^(9/2)/sqrt(log n_j) E_{x,y} d_j(x,y).

There is no restriction on the dimension of H or on matrix ranks. Negative type means squared Hilbert distance, and d_j itself is a metric. This is an existence statement, not an efficient construction statement. It gives the same lower bound on bi-Lipschitz distortion.

The new candidate operation is a dimension-independent spectral selection among many charts. Scalar Gaussian moments are matched before the target matrices are chosen; their operator-valued consequences are thus uniform over all matrix dimensions. A positive Gaussian dual pairing permits chart selection with matrix spectral projections. The source supplies the multichart kernel, local coordinate profiles, triangle repair, smoothing/coarea and uniform-copy mechanism. Their parameters are explicitly adjusted here.

All logarithms below are natural. Constants denoted C,c are absolute and may change. We take m sufficiently large and set

    N=m^6, q=ceil(log N), S=m^(10q),
    a=m^-40, b=m^40, epsilon=m^-200/S,
    r=m^-8, tau=m^-2000/S^2, lambda=m^-2.

## 1. Operator Gaussian moments

**Lemma1.** If X_1,...,X_m are selfadjoint matrices with sum_j X_j^2 <= I, and g_j are independent standard real Gaussians, then

    0 <= E(sum_j g_j X_j)^(2q) <= (2q-1)!! I.

Proof. Apply the ordinary scalar Wick formula to the expansion. For a fixed pairing pi of positions1,...,2q, the associated matrix is the sum of all words whose paired positions carry the same index. Its norm is at most1, as follows.

Write V:H -> C^m tensor H, Vh=sum_i e_i tensor X_i h. Then V*V=sum_i X_i^2<=I. Process the positions of the word from right to left. Maintain one C^m register for each pair with exactly one occurrence already processed. At a first occurrence, tensor the identity on all old registers with V, inserting a new register. At the matching occurrence, move its register next to H by a unitary permutation and apply V*, leaving every other register intact. Every map has norm at most1. The final space is H. Expansion of the maps gives precisely the pairing's summed matrix word: the new register sums its index, and its deletion enforces equality with the matching occurrence. Thus that word sum has norm at most1, whether or not it is positive. Summing over (2q-1)!! pairings bounds the norm of the expectation. The expectation is positive because each even power is positive, giving the Loewner bound. This argument does not substitute a trace inequality for an operator inequality. QED.

## 2. Finite directions universal for matrix tuples

Choose SN independent standard Gaussian vectors g_si in R^m, and put u_si=g_si/sqrt m. In addition to all the source directions lemma's per-chart properties, we require

    (SN)^-1 sum_{s,i} (sum_j u_sij X_j)^(2q)
        <= (4q/m)^q I                                      (2.1)

for every selfadjoint matrix tuple of every dimension with sum X_j^2<=I. We prove simultaneous existence without a matrix-dimensional net.

For each ordered word alpha=(j_1,...,j_{2q}) in [m]^(2q), truncate the scalar monomial G_{j_1}...G_{j_{2q}} at ||G||<=2sqrt m. Its absolute value is at most B=(2sqrt m)^(2q). Gaussian radial tails and Cauchy--Schwarz bound its truncation bias by

    (E||G||^(4q))^(1/2) P{||G||>2sqrt m}^(1/2)
      <= (C m)^q exp(-c m),

because q=O(log m). This is smaller than m^(-3q) for large m. Hoeffding applied with tolerance m^(-3q) and R=SN=m^(10q+6) samples has failure probability at most

    2 exp[-c R m^(-6q)/(16^q m^(2q))]
      =2 exp[-c m^(2q+6)/16^q].

Union over m^(2q) ordered words still tends to zero. Also R times the Gaussian probability of ||G|| outside [sqrt m/2,2sqrt m] tends to zero, since log R=O((log m)^2). Thus, with probability tending to1, every untruncated empirical monomial differs from its exact Gaussian expectation by at most2m^(-3q), and every sample has the source norm bounds.

For any tuple as in (2.1), each ||X_j||<=1. Expanding the noncommutative polynomial and using the scalar coefficient error bounds shows that the operator norm of its empirical-minus-Gaussian moment, after dividing by m^q, is at most

    m^(-q) m^(2q) 2m^(-3q)=2m^(-2q).

Lemma1 bounds the exact normalized Gaussian moment by (2q-1)!!/m^q I. The sum of this and the scalar error is at most (4q/m)^q I. This proves (2.1) uniformly over the matrix dimension and tuple.

The source per-chart covariance and Fourier-profile events still hold for this S. Precisely, directions-proof.tex bounds Fourier/covariance deviations by exp[-c m^4+O(m log m)+log S], and the norm-event failure by SN exp(-c m). These tend to zero for log S=O((log m)^2). Pairwise nonparallelism within each chart is almost sure. If its scalar majority-good-chart property is retained, its failure bound is at most exp[O(m log m)] 2^S (2m^-44)^(S/2), also tending to zero; our matrix proof does not require this last property. Intersect these events with the moment event. Fix one outcome for each sufficiently large m.

In particular, with J_s rows u_si, the source covariance/pseudoinverse conclusions remain

    N/(2m) I <= J_s*J_s <=2N/m I,
    ||J_s^+|| <=2sqrt(m/N),   ||J_s^+ e_i|| <=4m/N.

## 3. Matrix chart selection

**Lemma2.** Suppose the chosen directions satisfy (2.1). Let A_j and A_sj be selfadjoint D-by-D matrices. Suppose

    A_sj=sum_i u_sij b_si,
    ||b_si||_1<=t,
    sum_j ||A_sj-A_j||_1<=e       for each s.

Then

    E_g ||sum_j g_j A_j||_1 <= C Nt sqrt(q/m)+2e.             (3.1)

Proof. Set A(g)=sum g_j A_j, U(g)=sign(A(g)), with sign(0)=0, and X_j=E[g_j U(g)]. These are selfadjoint. For v in C^D, Bessel's inequality for the orthonormal scalar functions g_j in Gaussian L2, applied to the vector-valued function U(g)v, gives

    sum_j ||X_j v||^2 <= E||U(g)v||^2 <= ||v||^2.

Thus sum X_j^2<=I. More importantly,

    Y=sum_j A_j X_j=E[A(g)sign(A(g))]=E|A(g)| >=0,
    Tr Y=E||A(g)||_1.                                      (3.2)

Let Z_si=sum_j u_sij X_j and Q_s=(sum_i Z_si^(2q))^(1/q). Operator concavity of x^(1/q) and (2.1) imply

    S^-1 sum_s Q_s <= [(S^-1)sum_si Z_si^(2q)]^(1/q)
       <= N^(1/q) (4q/m) I <= 4euler q/m I,

where euler=exp(1), since q>=log N. Take h=8euler q/m and let P_s=1_[0,h](Q_s). Functional calculus gives I-P_s<=Q_s/h, so sum_s P_s>=S I/2.

For every i, Z_si^(2q)<=sum_i Z_si^(2q)=Q_s^q. The Loewner--Heinz monotonicity of x^(1/q) gives Z_si^2<=Q_s. Hence

    ||Z_si P_s||^2=||P_s Z_si^2 P_s||<=h.

Using positivity (3.2), trace duality and the representation of A_sj,

    (S/2)Tr Y <= sum_s Tr(Y P_s)
       = sum_si Tr(b_si Z_si P_s)
          + sum_sj Tr((A_j-A_sj)X_j P_s)
       <= SNt sqrt h + Se.

For the last term use ||X_j P_s||<=1. Although some summands may be complex, their sum is real, and bounding their absolute values is valid. This proves (3.1). QED.

This positivity step is what permits noncommuting chart selectors. Selecting a single chart by an operator-norm net would instead incur a target-dimension dependence; no such net is used here.

## 4. Parameter-compatible negative-type metric

We apply the actual construction in source117-1 kernel.tex, repair.tex and metric.tex with the directions above and the parameters displayed before §1. We detail the changed S dependence rather than invoking the original fixed-S proposition unchanged.

For clarity the reused feature formulas are as follows. Write E(t)=(cos t,sin t), let gamma_m be standard Gaussian measure, and take the real Hilbert sum

    L2([a,b] x R^m, d sigma d gamma_m; R²)
       direct-sum over(s,i) L2([a,b], d sigma/sigma; R²).

The first component of p(theta) is m^(1/4) E(<g,theta>/sigma), and component(s,i) is sqrt(epsilon) E(<g_si,theta>/sigma). The preliminary A_s^0(theta)e_i is supported only in block(s,i), with value (m/N)epsilon^(-1/2) E'(<g_si,theta>/sigma). These are the pinned construction's formulas with the new parameters, not new kernel operations.

The common feature map p has the source Gaussian block and one Fourier block of amplitude sqrt(epsilon) for each (s,i). Its squared-distance error from c_* sqrt m ||theta-eta|| is bounded by

    2sqrt m a +36m^(3/2)/b +4epsilon SN log(b/a)
      <= m^-37,

since epsilon SN=m^-194. Its auxiliary derivative contribution is bounded by epsilon SN log(b/a)(2sqrt m/a)^(2j), j=0,1,2. Consequently the same ||D^j p||<=m^110 bounds hold.

The preliminary chart extension A_s^0 has column amplitude (m/N)epsilon^(-1/2), now sqrt S times the old polynomial amplitude. The source formulas

    R_s=Dp-A_s^0 J_s,
    A_s=A_s^0(I-J_s J_s^+)+Dp J_s^+

still give A_s J_s=Dp. Its profile against p(eta) is unchanged in the main term because sqrt(epsilon) cancels epsilon^(-1/2). The residual Fourier profile has norm at most

    2epsilon SN sqrt m/a <=1.

The source Fourier-approximation error therefore still gives

    |<A_s(theta)e_i,p(eta)>| <= C(m/N)log m.

The five strong bounds in ker:strong-bounds can all be taken to be sqrt S m^300: p,Dp,D²p remain bounded by m^110; A_s^0 and DA_s^0 gain sqrt S, and the exact formula above with the source J_s,J_s^+ bounds gives the asserted common bound.

Round labels by X_s(theta)_i=tau floor(<u_si,theta>/tau). Set Q_s^geom=I-J_s J_s^+ and

    P_s(x)=p(J_s^+x)+A_s(J_s^+x)Q_s^geom x.

(The geometric Q_s is unrelated to the matrix selector Q_s of §3.) The source rounding errors are unchanged:

    ||x-J_s theta||<=sqrt N tau,
    ||J_s^+x-theta||<=2sqrt m tau,
    ||Q_s^geom x||<=sqrt N tau.

Thus the feature error is <=sqrt S m^305 tau. A deliberately loose bound for the squared-distance error is S m^610 tau; with tau=m^-2000/S² this is negligible compared with r=m^-8. The source global angle estimate remains >=-r.

For coordinate profiles along any same-chart label segment, differentiating P_s yields the source identity

    DP_s(x)h=A_s(J_s^+x)h
              +DA_s(J_s^+x)[J_s^+h]Q_s^geom x.

The derivative error is <=sqrt S m^305 tau. Pairing with p or a rounded feature and using the strong bounds gives profile error at most C S m^610 tau, which is smaller than (m/N)log m. Hence the same local-angle bound holds with L=C0 log m:

    |<P_v-P_z,P_y-P_z>| <= L(m/N)||x_v-x_z||_1.

Set delta(v,w)=L(m/N)||x_v-x_w||_1 within a chart and infinity across charts. The source triangle-repair lemma, valid for arbitrarily many charts, appends Hilbert vectors whose squared distances are

    8 int_0^r [1-exp(-delta(v,w)/ell)] d ell.

Therefore d(v,w) is squared Hilbert distance and satisfies every triangle inequality. It is positive for distinct labels: within a chart delta>0, and between charts the appended distance is8r. Thus the original label set already carries a genuine metric.

For adjacent labels (one coordinate changes by tau),

    d(v,w) <= C tau(m/N) log m [1+log(r/(L(m/N)tau))]
            <= C tau(m/N)(log m)^3.                         (4.1)

Indeed log S=O((log m)^2), so log(r/(L(m/N)tau))=O((log m)^2). The source macro estimate remains

    |d(v_s(theta),v_t(eta))-c_*sqrt m ||theta-eta|||<=Cr.      (4.2)

The number of threshold hyperplanes in each chart is at most H0=N(1+8sqrt m/tau). Its logarithm is O((log m)^2). The arrangement count gives

    |V| <= S sum_{k=0}^m binom(H0,k)
          <= exp(C m(log m)^2).                             (4.3)

The source diameter and first-chart average proofs, using (4.2), give diam(V,d)<=Cm and E_{theta,eta uniform T} d(v_1(theta),v_1(eta))>=cm, where T=(-1,1)^m.

## 5. Contraction into arbitrary finite matrices

First suppose F takes selfadjoint matrix values and is nonexpanding. Put f_s(theta)=F(v_s(theta)), with the same piecewise-constant labels, and smooth by the source product kernel kappa_lambda, lambda=m^-2. For theta in T the smoothing only sees U=(-2,2)^m. Let H_s=f_s*kappa_lambda.

The norm estimates preceding the source scalar-coordinate argument use the triangle inequality, coarea and integration of a norm. They are valid for trace-norm-valued functions. Equation (4.2) gives

    ||H_s(theta)-f_s(theta)||_1 <= C(m lambda+r),
    ||partial_j H_s(theta)-partial_j H_1(theta)||_1<=Cr/lambda. (5.1)

For explicitness, the first follows by integrating the displacement bound Csqrt m ||z||+Cr with coordinate displacements O(lambda). The second differentiates the common smoothing kernel and uses ||f_s-f_1||_1<=Cr pointwise with ||partial_j kappa_lambda||_1<=C/lambda.

Coarea across the interfaces <u_si,theta>=k tau yields

    partial_j H_s(theta)=sum_i u_sij b_si(theta).

The jump at an interface has trace norm at most Ctau(m/N)(log m)^3 by (4.1). The source coarea density h for <u_si,Z> satisfies int|h'|<=Csqrt m/lambda and tau sum_k h(k tau)<=1+Ctau sqrt m/lambda<=2. Integrating the jumps, with nonnegative smoothing weight, therefore gives the POINTWISE bound

    ||b_si(theta)||_1<=C(m/N)(log m)^3.                     (5.2)

More explicitly, b_si is the sum over interfaces of the signed jump, integrated against kappa_lambda(theta-z) dH^(m-1)(z)/||u_si||. Intersections of two nonparallel interfaces have surface measure zero. Coarea identifies the total scalar weight on the k-th hyperplane with the density h at the appropriate translated k tau. For that density, choose a coordinate with |u_sij|>=1/(2sqrt m), condition on all other coordinates, and differentiate its rescaled one-dimensional kernel. This gives int|h'|<=Csqrt m/lambda. The Riemann-sum error bound tau sum_k h(t+k tau)<=int h+tau int|h'| then gives the stated total weight. Thus (5.2) follows directly without a scalar coordinate decomposition of the target.

No positivity of these matrices is asserted or required. Their selfadjointness follows from that of F. Equations (5.1) imply the error parameter in Lemma2 is e<=Cmr/lambda=Cm^-5. Applying Lemma2 at each theta gives

    E_g ||sum_j g_j partial_j H_1(theta)||_1
       <= Csqrt m (log m)^(7/2).                           (5.3)

We need a Banach-valued rather than scalar-component cube Poincare inequality. For any smooth B-valued h on T,

    E_{theta,eta uniform T} ||h(theta)-h(eta)||_B
       <= C E_theta E_g ||sum_j g_j partial_j h(theta)||_B. (5.4)

Here is a direct proof. Let G,G' be independent standard Gaussian vectors, let G(t)=cos(t)G+sin(t)G', and W(t)=-sin(t)G+cos(t)G', 0<=t<=pi/2. For each t, G(t),W(t) are independent standard Gaussians. Set theta_j(t)=2Phi(G_j(t))-1, with Phi the standard Gaussian distribution function. The endpoints are independent uniform points of T. Differentiate h(theta(t)), integrate its norm, and condition on G(t). Its derivative is sum_j 2phi(G_j(t)) W_j(t) partial_j h(theta(t)). Since 0<=2phi<=sqrt(2/pi), the Gaussian contraction principle for any norm bounds the conditional expectation by sqrt(2/pi) E_g||sum g_j partial_j h(theta(t))||. That principle follows by adding independent Gaussian noise to the smaller diagonal-covariance vector and Jensen's inequality. Integration in t proves (5.4). All functions here are finite-dimensional smooth and bounded on the relevant cube, so the operations are justified.

Combining (5.1),(5.3),(5.4),

    E_{theta,eta} ||F(v_1(theta))-F(v_1(eta))||_1
          <= Csqrt m(log m)^(7/2).                         (5.5)

For arbitrary complex matrices use the Hermitian dilation D(B)=[[0,B],[B*,0]]. It is real-linear and ||D(B)||_1=2||B||_1. Applying the selfadjoint conclusion to D(F)/2 gives (5.5) with the same form of absolute constant. Thus no selfadjointness restriction survives in the theorem.

## 6. Uniform points and strictly positive distances

Let w_v=P{v_1(theta)=v}, retaining every auxiliary vertex even if w_v=0. Take

    M=m^m+m²|V|, k_v=1+floor(M w_v), n=sum_v k_v,
    mu_v=k_v/n.

Then M<=n<=M+|V| and TV(mu,w)<=|V|/M<=m^-2. For any nonexpanding F, its pairwise norm distances are at most diam d<=Cm. The TV distance between the two product laws is at most2m^-2. Consequently (5.5) holds with mu in place of w, up to an additive O(1/m), and the mu-average metric distance is still at least cm. In particular

    E_{v,w~mu} ||F(v)-F(w)||_1<=Csqrt m(log m)^(7/2),
    E_{v,w~mu} d(v,w)>=cm.                                (6.1)

Make k_v copies of each v. Let d0 be the pullback pseudometric. To obtain a genuine metric, let d_min be the smallest distance between distinct original labels and choose

    0<zeta<=min(1,d_min)/m².

Define d'(x,y)=d0(x,y)+zeta for x!=y and d'(x,x)=0. The added equilateral metric is squared Hilbert distance, so d' is negative type and is a genuine metric.

If F on these n points is nonexpanding for d', choose one representative x_v per group. Then G(v)=F(x_v) is (1+m^-2)-Lipschitz for d. Each copy value differs from its representative by at most zeta. Applying (6.1) to G/(1+m^-2) gives

    E_{x,y uniform} ||F(x)-F(y)||_1
         <=(1+m^-2) Csqrt m(log m)^(7/2)+2zeta,
    E_{x,y uniform} d'(x,y)>=cm.                           (6.2)

The vertex count satisfies

    m^m<=n<=exp(C m(log m)^2).

Thus loglog n>=log m for large m and sqrt(log n)<=C sqrt m log m. It follows from (6.2) that the first-average distortion is at least

    c sqrt m/(log m)^(7/2)
       >= c' sqrt(log n)/(loglog n)^(9/2).

These n tend to infinity with m. No map-dependent choice enters the constructed metric.

## 7. Infinite-dimensional trace class

For finitely many trace-class operators F(x) on any complex Hilbert H, their ranges and adjoint ranges lie in one separable closed subspace. Let P_k be finite-rank orthogonal projections increasing strongly to the identity on that subspace. Then ||P_k F(x)P_k-F(x)||_1 tends to0 for every x. Compression is trace-norm contractive, so each compressed map is nonexpanding and satisfies the finite-matrix bound with the same constants. Passing to the limit in the finite pair sum proves the statement for S_1(H), even if H itself is nonseparable. This completes the author-side proof at the frozen scope.

## 8. Fractional powers used in the selector

For completeness, both operator properties used in §3 follow from the standard integral representation, for0<alpha<1,

    T^alpha = [sin(pi alpha)/pi] int_0^infinity
                 T(T+sI)^(-1) s^(alpha-1) ds.

The resolvent inverse reverses Loewner order, so T(T+sI)^(-1)=I-s(T+sI)^(-1) is operator monotone. The inverse is operator convex, so the same expression is operator concave. Integration gives both properties, and continuity extends them to positive semidefinite matrices. Alpha=1 is immediate. This also clarifies that no simultaneous diagonalization of the different chart matrices is assumed.

## Dependencies, contribution and limits

Source117-1: directions/covariance and empirical Fourier approximation; common Gaussian/Fourier kernel; exact chart derivative extension; tiny-mesh angle estimates; chartwise Schoenberg-kernel triangle repair; hyperplane region count; norm/coarea smoothing; weighted first-chart distribution and copy conversion. All mathematical bodies of this companion were read. Their truth is stipulated; the changed S,epsilon,tau dependence is the new audit above.

Source117-2: actual main and introduction state scalar uniform-sparsest-cut constant-factor hardness and describe its finite predicate/entropy/path construction. Its full operative proof was not read; a targeted search found no Schatten/noncommutative/matrix-valued target. It is not a dependency of the proof.

Standard tools: Wick expansion, row/column contractions, operator monotonicity and concavity of fractional powers, Bessel and trace duality, Gaussian rotation Poincare, Hoeffding, finite-rank trace-class approximation. These are not claimed new. Parent independently checked the register contraction idea and spectral cutoff step and supplied an alternate Gaussian-chaos argument. Parent assistance is author collaboration, not independent review.

Actual primary comparisons include KNT2021's snowflaked Schatten embedding and LWW2026's noncommutative Talagrand inequality. Neither is claimed to be disproved or superseded: their hypotheses and outputs differ. A broader literature review may still identify an antecedent for this construction. No global priority claim, formal proof claim, independent PASS or campaign count credit is made here.
