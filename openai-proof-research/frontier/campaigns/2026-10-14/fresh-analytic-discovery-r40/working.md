# Family344: the exact-period barrier and a global curvature diagnostic

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Author-side screen only. The full problem in original-scope.md is unresolved. The auxiliary result below is a technical obstruction to one proof route, not a substitute nominee.

## 1. What the stipulated source actually gives

At the immutable pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, family344 has one manuscript directory, The-metric-Blaschke-theorem-September-23-2026. Its exact theorem assumes global inj=diam. Section01 obtains a common cut distance D, a common prime geodesic period T=2D, a great-sphere cut fibration, and constant angular nullity k. In the intermediate projective cases these are INPUTS to the analytic comparison.

Section02 differentiates phi_T=Id on SM to obtain periodicity of EVERY normal Jacobi field, including its derivative. It then proves the intersection pattern dim(L_x cap L_y)=k at separation D and zero at all other separations modulo T. The fixed graph chart and its Schur block have sizes determined by this exact nullity. They are not constructed for an arbitrary manifold with cut times merely in [1-epsilon,1].

Section03 derives the scalar cancellation and uses four folded weights whose row and column sums agree exactly. It proves int w log(f/w)>=0. With Phi(r)=r-1-log r, it obtains

    int(f-w) = int w log(f/w) + int w Phi(f/w),

both right terms nonnegative. The constants bounding scalar profile ratios are allowed to depend on the selected geodesic. Section04 identifies the integral over SM as 2 T V(V-V0) by full-period polar integration and geodesic-flow invariance. At equality the strict remainder vanishes, every radial density equals the model density, and harmonic-manifold classification applies.

There are TWO missing interfaces for an almost theorem. First, construct approximate replacements for the exact-period/nullity/folding data, with an error controlled only by dimension and epsilon. Second, bound the resulting normalized defect from above by a quantity tending to zero. The exact quaternionic upper bound uses a genuine incidence normal bundle and a free geodesic circle action; neither has been produced in the positive-deficit class. Even choosing the model type is part of the unresolved almost theorem. The source's V-V0 is not an a priori function of diam-inj on this larger class. Its strict convexity cannot by itself supply that function.

The elementary algebraic estimate

    Phi(r) >= (r-1)^2 / (2 max(1,r))  (r>0)

follows by integrating Phi''(r)=1/r^2 (or differentiating the displayed comparison on each side of 1). Thus Cauchy--Schwarz would bound an L1 density error by the square root of a known integrated defect times a known mass bound. This is a paid scalar estimate, conditional on unavailable geometric inputs; it does not establish almost-Blaschke rigidity. No nomination is made from it.

## 2. A complete technical example: global near equality does not bound curvature

For every fixed n>=2 there are smooth metrics g_r on S^n, r decreasing to zero, such that

    diam(g_r)/inj(g_r) -> 1,
    g_r -> g_round in C1,
    sup |sec(g_r)| -> infinity.

After constant rescaling to diameter one, the same assertions about the ratio and unbounded curvature hold. In fact their GH distance to the normalized round sphere tends to zero. Therefore this example does NOT refute the full GH target; it excludes deducing a uniform sectional-curvature bound, or smooth compactness from that bound, merely from small radius deficit.

### Construction and elementary bounds

Let g0 be the sectional-curvature-one round metric on S^n, p a fixed point, and x normal coordinates at p. Choose chi in C_c^infinity(B_1(0)), equal to -|x|^2 near zero. Define

    a=r^(3/2),   phi_r(x)=a chi(x/r),   g_r=e^(2 phi_r) g0,

extending phi_r by zero. Constants below depend only on n and chi. Then

    ||phi_r||infinity <= C a,
    ||d phi_r||infinity <= C a/r,
    ||D² phi_r||infinity <= C a/r².

Consequently g_r tends to g0 in C1, and pointwise metric comparison gives

    e^(-Ca) d0 <= d_r <= e^(Ca) d0,
    e^(-Ca) pi <= diam(g_r) <= e^(Ca) pi.                 (2.1)

At p, phi_r=0, d phi_r=0, and Hess(phi_r)=-2a r^(-2) g0. The conformal sectional-curvature formula gives, for every orthonormal two-plane at p,

    sec(g_r)(p)=1+4a/r²=1+4r^(-1/2).                     (2.2)

Everywhere, curvature as an operator differs from the constant-curvature-one operator by at most C a/r² on B_r(p), and agrees with it outside that ball. Terms a and (a/r)^2 are smaller than a/r² for small r.

### Uniform crossing-time bound

For every unit-speed g_r geodesic gamma, every connected component of the time spent in B_r(p) has length at most C r. Indeed F=d0(p,.)² has Hess_g0 F=2g0+O(r²) in that ball. The connection change is bounded by C|d phi_r|, so

    Hess_gr F = Hess_g0 F - dF(connection change)
              = 2g0 + O(r²+a) >= g_r

for small r. Along gamma, F''>=1. If an interval [u,v] lies inside the ball, 0<=F<=r². Applying the midpoint convexity estimate to F(t)-t²/2 gives

    (v-u)²/8 <= (F(u)+F(v))/2 - F((u+v)/2) <= r²,

hence v-u<=sqrt(8)r, by limiting endpoints if necessary. This also rules out a geodesic remaining in the ball forever.

Between visits, gamma is a unit-speed round great circle. A great circle intersects a round ball of radius r<pi/2 in at most one arc per period, of length at most 2r. After an outgoing crossing, its next incoming crossing is therefore at least 2pi-2r later, or never if tangent without entering. It follows that on any time interval of length 2pi the geodesic has at most two interior visits (partial endpoint visits included). Tangencies contribute zero length. The total time in the support is at most C r.

In any g_r-parallel orthonormal normal frame along gamma, the radial curvature matrix is

    R_gamma(t)=Id+E_gamma(t),
    int_0^(2pi) ||E_gamma(t)|| dt <= C a/r =: eta_r.       (2.3)

No pointwise upper curvature estimate independent of r is used; eta_r=C sqrt(r) tends to zero.

### Conjugate radius estimate

Let A''+(Id+E)A=0, A(0)=0, A'(0)=Id. Variation of constants gives

    A(t)=sin(t)Id-int_0^t sin(t-s)E(s)A(s) ds.             (2.4)

The first-order system and Gronwall with int||E||<=eta_r give ||A(t)||+||A'(t)||<=C on [0,2pi], uniformly for small r. Since A(0)=0, also ||A(s)||<=C s. Dividing (2.4) by t, and using |sin(t-s)|<=1, s<=t, yields

    ||A(t)/t - (sin t/t)Id|| <= C eta_r,  0<t<=pi.        (2.5)

For 0<t<=pi-delta, sin(t)/t>=c delta when 0<delta<1 (with the continuous value 1 at t=0). Choose delta=C0 eta_r, with C0 larger than the ratio of the constants in (2.5). Then A(t) is invertible throughout 0<t<=pi-C0 eta_r. This is uniform over all starting points and directions. Thus

    conj(g_r) >= pi-C eta_r.                              (2.6)

### Closed-geodesic estimate

The geodesic sprays of g_r and g0, on a fixed compact annulus of tangent vectors, differ by O(a/r). Comparison with the smooth round spray and Gronwall give, on every time interval of length 2pi, position and velocity differences O(a/r), after normalizing the same initial direction to round unit speed. This uses a uniform sup difference of sprays and the Lipschitz constant of the ROUND spray, not a uniform derivative bound for the perturbed spray.

There is a uniform lower bound l0>0 on lengths of nonconstant closed unit-speed g_r geodesics: their ambient accelerations in R^(n+1) are uniformly bounded because the metrics are C1 close, while their initial ambient speeds are bounded below. On a sufficiently small fixed interval the displacement has a positive component in the initial velocity direction. A closed geodesic cannot have such a length.

If a closed unit-speed g_r geodesic has length L<=2pi, comparison to the round great circle therefore gives

    2 sin(L/2) <= C a/r,   l0<=L<=2pi.

For small r this implies L>=2pi-C a/r. Geodesics longer than 2pi already satisfy that lower bound. Hence

    length(shortest closed geodesic of g_r) >= 2pi-C eta_r. (2.7)

The compact-manifold injectivity-radius identity (Klingenberg: the minimum of conjugate radius and half the shortest closed-geodesic length), explicitly stated in Shankar--Spatzier--Wilking, arXiv:math/0305177v1, Section1 p3, now combines (2.6)--(2.7) to give

    inj(g_r) >= pi-C sqrt(r).                              (2.8)

Together (2.1),(2.2),(2.8) prove the example. A constant metric rescaling by diam(g_r)^(-2) normalizes the diameter; its curvature multiplier tends to pi², so curvature remains unbounded. The same rescaling and (2.1) give uniform convergence of the normalized distances to round normalized distances, hence GH convergence. QED.

### Limits of the example

The example attacks only a curvature-based compactness shortcut. It does not show failure of GH precompactness in the almost-equality regime, absence of a different compactness theorem, or failure of a direct distance comparison. It does not contradict exact rigidity: every member has positive deficit unless it is round, and the sequence has precisely the predicted round GH limit. It is a standard localized metric perturbation, classified TECHNICAL author-side; it is not proposed for the campaign count.

## 3. Primary operations and remaining route

Durumeric's 1982 dissertation, scanned pages72--73 (PDF80--81), Example2, stretches a ball about ONE prescribed point p on an arbitrary compact manifold. It gives i_p/d_p arbitrarily close to one. This does not give a lower bound for the global inf_q i_q divided by the global diameter. The global corollaries on page76 (PDF84) retain a lower sectional-curvature parameter. Example3, pages74--75, is the flat hexagonal torus with ratio sqrt(3)/2, a fixed gap from one. Neither example disproves the full problem here.

Durumeric arXiv:math/0204050v1, p2, says a positive lower i(M)/d(M) ratio alone does not provide GH precompactness without curvature restrictions. That statement concerns a positive lower ratio, not necessarily ratios approaching one. It is not treated as a counterexample in the limiting regime.

Shankar--Spatzier--Wilking's Section1 begins with sec<=1 and a conjugate point exactly at pi along every geodesic. Its rigidity uses those hypotheses, Rauch equality, and exact periodic-geodesic arguments. The compact injectivity-radius identity used above is general, but their main rigidity theorem cannot simply be applied to arbitrary positive-deficit metrics.

A credible next operation for the FULL problem must control distances or construct the required approximate return/cut-incidence geometry without obtaining a false uniform curvature bound. The example shows that an L1-in-time radial curvature error CAN suffice to control conjugate times in a perturbative model. The premise inj>=1-epsilon, diam=1 does not presently supply that L1 error relative to any model, nor a model identification. Trying to infer pointwise radial curvature from a conjugate-time pinching is an inverse Sturm problem with far less data than the forward estimate (2.4). No such inverse estimate, multiscale distance construction, or general precompactness/classification of possible nonsmooth limits has been proved here.

Consequently the full problem remains unresolved. There is no source refutation, no candidate proof, no contribution pass, and no count.
