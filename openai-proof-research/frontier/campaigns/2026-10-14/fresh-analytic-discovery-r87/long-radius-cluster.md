# Long-radius cluster estimate with support-size loss

This author supporting lemma retains the full unresolved target. It is not a deterministic multi-cluster summation theorem.

Let1<q<3/2, epsilon>0. Fix a radial annular multiplier P=p(D) supported in1/2<|xi|<3. Suppose F(r,z) is supported in r∈[R,2R] and z in one cube of side L>=2, and R>=C L^4. Then

 ||integral_R^{2R} P(sigma_r*F(r,.))dr||_{Lq({cR<|x-z0|<CR})}
 <= C_(q,epsilon,c,C) R^(3/q) L^epsilon ||F||_{Lq_z L2(dr/r)}.     (CL)

Here z0 is the cube center and0<c<C<infinity are fixed; one may translate z0 to zero. The conclusion concerns a fixed comparable-radius output shell only. It is not yet a bound over all x, nor a sum over j. We retain both signs of the spherical kernel and P's physical tails. The following argument gives a derivation from the preceding localized vector restriction lemma.

## 1. Continuum version of the supporting restriction bound

For a(t,z) on a fixed compact frequency set bounded away from zero, with z supported in the cube, the finite-family lemma implies

 || integral |ahat_t(t omega)|² dt ||_{L^(q/2)(S²)}^(1/2)
 <= C_(q,epsilon) L^epsilon ||a||_{Lq_z L2_t}.                    (VRc)

To justify this without an unproved vector extension, first take functions simple in t and approximate t in the Fourier kernel by a representative t_k on each interval. The finite-family estimate applies with coefficients sqrt(|I_k|) a_k(z). The kernel error is bounded in Lq_omega L2_t by mesh*sup|z| times integral ||a(.,z)||_2 dz, which tends to zero for fixed L. Simple functions are dense in Lq_z L2_t, and the same finite-volume bound controls the operator on differences before taking limits. A finite partition of the fixed frequency set into positive/negative intervals with ratio at most2 handles the frequency ranges other than[1,2]. Spatial rescaling and reflection change only fixed constants.

## 2. Exact removal of irrelevant radial frequencies

Extend F by zero to all real r. Choose a smooth compactly supported even multiplier b(t), supported away from zero, equal one on a neighborhood of supp p and its reflection. Let H=b(D_r)F. In particular ||H||_{Lq_z L2_r}<=C||F||_{Lq_z L2_r}. The Fourier transform of sigma_|r| is4pi r sin(r|xi|)/|xi|. Thus

 integral_R^{2R} P(sigma_r*F(r,.))dr
 = integral_R P(sigma_|r|*H(r,.))dr.                             (7)

Indeed, in the spatial Fourier transform, integration against r exp(±ir|xi|) evaluates a radial-frequency derivative of Fhat_r at±|xi|. Multiplication by b leaves both these values and derivatives unchanged on supp p, because b=1 and b'=0 there. Formula(7) initially holds for smooth compactly supported data and then by the bounds below. It is an exact frequency identity, not an assumption that radial convolution preserves [R,2R].

The coarea identity turns its right side before P into

 integral [H(|x-z|,z)+H(-|x-z|,z)]dz.                            (8)

Consequently both outgoing and incoming radial profiles must be treated.

## 3. Far-field comparison in the radial L2 norm

Write x=rho omega, rho∈[cR,CR]. Let kappa=F^{-1}p. In(8) after P replace x by x-w and integrate against kappa(w). For |z+w|<=cR/4, the map

 d(rho)=|rho omega-z-w|

has derivative bounded above and below by positive constants and

 |d(rho)-(rho-omega.(z+w))|<=C_c |z+w|²/R.

A fundamental-theorem-of-calculus argument for composition with these uniformly increasing maps yields

 ||H(±d(rho),z)-H(±(rho-omega.(z+w)),z)||_{L2_rho([cR,CR])}
 <= C_c |z+w|²/R ||partial_r H(.,z)||_2
 <= C |z+w|²/R ||H(.,z)||_2.                                  (9)

The last inequality uses H's fixed compact radial Fourier support. To spell out the first inequality: interpolate between the two arguments; every interpolating derivative remains bounded below, so the change of variables in the integral of |H'|² is uniform, and Minkowski integrates the interpolation parameter.

Integrate(9) against |kappa(w)| for |w|<=cR/8, choosing the constant in R>=C L^4 large enough to include z. The finite second moment gives C L²/R. For |w|>cR/8, use the one-dimensional band-limited bound ||H(.,z)||_infinity<=C||H(.,z)||_2. Even if the distance map has a turning point there, its restriction to an interval of length O(R) has L2 norm at most C sqrt(R)||H(.,z)||_2. Schwartz tails of kappa therefore give O_N(R^(-N+1/2)), with N arbitrarily large. No unsupported global Jacobian bound is used in this region.

Thus the radial L2 error, uniformly in omega, is at most

 C L²/R integral ||H(.,z)||_2 dz
 <= C L^(5-3/q)/R ||H||_{Lq_z L2_r}.                            (10)

## 4. Main term and conversion to the physical shell norm

For the positive sign, express H(r,z) by its radial Fourier transform a(t,z). The main term after the w integration is

 integral exp(it rho) p(t omega) [integral exp(-it omega.z)a(t,z)dz]dt.

Because p is radial, p(t omega)=p(|t|), a bounded scalar multiplier. The negative sign gives the corresponding reflected frequency expression. Plancherel in rho and(VRc) bound the main term in Lq_omega L2_rho(R) by

 C_(q,epsilon) L^epsilon ||H||_{Lq_z L2_r}.

For q<2, Holder on the radial interval of length O(R), followed by rho²<=C R², gives

 ||G||_{Lq(shell)} <= C R^(3/q-1/2) ||G||_{Lq_omega L2_rho}.

Finally ||H||_{Lq_z L2_r}<=C sqrt(R)||F||_{Lq_z L2(dr/r)}, since the original F is supported in[R,2R]. Combining this with(10) yields

 ||B_R F||_{Lq(shell)}
 <= C R^(3/q) [C_(q,epsilon)L^epsilon+L^(5-3/q)/R] ||F||_{Lq(H)}.

Under R>=C L^4 the error is bounded, giving(CL). Spatial smooth approximation justifies all initially formal integral identities. The finite source(1) estimate in the companion lemma and the displayed bounds control the limits.

## 5. Remaining global obligations

(CL) is uniform in the very large radius R once the cluster diameter is bounded, replacing the former R^epsilon loss by L^epsilon. It is valid for arbitrary radial H profiles, not just finitely many modulations. But it is only a comparable-radius shell estimate for one cluster. Near and distant output tails, multiple spatial clusters, and the full sum over dyadic R are not declared paid here.

In particular, two output waves from different clusters generally overlap on sets of volume comparable to R³. Pointwise summing their absolute values sacrifices cancellation. An L2 cross-term estimate is still valid between well-separated inputs, but one cannot combine it with these Lq diagonal bounds merely by truncating each output: truncation changes cross terms. The next note states that obstruction explicitly.
