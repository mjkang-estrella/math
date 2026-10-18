# Critical maximal radial means: two proof routes and the remaining estimate

This is author discovery, not a full proof or nomination. Scope is fixed in scope-status.json. All source theorems are stipulated; no upstream audit is attempted.

## 1. The old restriction route has a sharp obstruction

Lee–Rogers–Seeger (LRS), arXiv1207.6582v1 Lemma2.2, uses Stein–Tomas to bound an integral of smoothed spherical surface measures at radii r in [R,2R] into L2, with RHS R^(3/2)||F||_{L^q_x L2(dr/r)}. Its allowed q<=4/3 is genuine, not merely an exponent left unoptimized. The following annular-frequency version makes the issue explicit. Constants 2pi are absorbed into the r parametrization.

Let P be a smooth frequency cutoff equal one near e1. Define

 A_R F = integral_R^{2R} r exp(i r|D|) P F(r,.) dr.

This is the outgoing term of the three-dimensional spherical convolution, up to a harmless annular multiplier |D|^(-1). Take a fixed smooth Fourier bump on the box |xi1-1|<=c/R, |xi2|,|xi3|<=c/sqrt(R), and let f_R be its inverse transform, normalized so its physical-space amplitude is order one. Then ||f_R||_q is comparable to R^(2/q), and ||f_R||_2 is comparable to R. On that box ||xi|-1|<=C c/R. Choose F(r,x)=exp(-ir) f_R(x). Its H=L2(dr/r) norm is a fixed constant times |f_R(x)|. For sufficiently small c, the real part of integral_R^{2R} r exp(ir(|xi|-1))dr is >=c0 R² throughout the box. Plancherel gives ||A_R F||_2 >=c1 R³.

Thus the claimed Lq(H)->L2 bound with factor R^(3/2) would require R³<=C R^(3/2+2/q), impossible for q>4/3. The unavoidable loss is at least R^(3/2-2/q). The same example works for the actual spherical kernel: its incoming term has r-phase derivative bounded away from zero and integral O(R), versus the outgoing R² term. The low-frequency cancellation cutoff can be chosen nonzero on this frequency box.

This disproves only that L2 intermediate estimate. It does not disprove the desired maximal theorem. The target p in (3,4] is dual to q in [4/3,3/2), exactly where this obstacle begins.

LRS proof equations(23)–(25) show the associated summation barrier explicitly. After discarding dense spatial cubes, the surviving count per radius-R cube is at most lambda^q. Their squared L2 bound is C lambda^(q/2) log(lambda) times sum_j 2^(3j)#E_j. Chebyshev needs lambda^(q/2-2)log(lambda)<=C lambda^(-q), hence q<4/3. Merely changing the target exponent in their stopping rule fails.

## 2. Source local smoothing gives a genuine replacement with a scale loss

Use the pinned companion full strict local-smoothing theorem, not just the scalar fixed-radius multiplier. If p>3 and P is fixed annular-frequency localization, scaling its frequency-R estimate from times [1,2] to [R,2R] gives

 ||exp(i r|D|)P g||_{Lp_x Lp([R,2R],dr/r)} <= C_(p,epsilon) R^(1-3/p+epsilon)||g||_p.

The bounded factor between dr/r and normalized dr does not depend on R. For p>2, Holder in r yields the same bound with inner L2. Dualizing against F with the H measure dr/r, the adjoint of A_R contains r² exp(-ir|D|)P*, not r exp(-ir|D|). Therefore, with q=p/(p-1),

 ||A_R F||_q <= C_(q,epsilon) R^(3/q+epsilon) ||F||_{Lq(H)},       1<q<3/2.

The exponent identity is 2+(1-3/p)=3/q. This is an actual new-to-this-checkpoint quantitative interface obtained by scaling and duality; it is a routine consequence, excluded as a nominee. It avoids the false L2 estimate above. A bounded t dilation in sigma_(rt) changes the time interval to [R,4R] and is handled by finitely many windows; integration against any probability measure in t is bounded by Minkowski.

The estimate is epsilon-loss at each radius block. The sought endpoint uses a sum over all blocks with no scale loss. Its model is LRS Proposition2.1 beyond the old q range:

 ||sum_j integral_[2^j,2^(j+1)] psi*sigma_r*eta*F_j(r,.) dr||_q
 <= C_q (sum_j 2^(3j) ||F_j||_{Lq(H)}^q)^(1/q).

For the maximal theorem one needs the version with arbitrary t-dependent F and the outer L1(dnu(t)) norm as well. The annular outgoing model above is only one part; low-frequency tails, both signs, and the radial multiplier reduction must also be retained. No equivalence to the full target is asserted from the model alone.

A direct triangle sum of the proved block estimates has summands 2^(epsilon j) a_j, where a_j=2^(3j/q)||F_j||_{Lq(H)}. It is not bounded by ||a||_ellq. Allowing epsilon to depend on j is invalid without quantitative control of C_(q,epsilon), which the source does not provide. Even an exactly lossless block estimate would leave an ell1 rather than ellq sum.

A possible epsilon-removal plan is to split j at N(lambda)=c log2(lambda) in the LRS restricted-weak proof. On the low j portion the factor 2^(epsilon j) costs only lambda^(c epsilon), potentially absorbable by choosing an interior exponent. But the large-j portion is still controlled in that proof by L2 diagonal energies plus pairwise spatial separation. The diagonal term obeys the old lambda^(q/2) barrier, and its L2 improvement is ruled out by the example above. New control of the sparse sum in an exponent different from 2, including cross-scale interactions, is required. Source local smoothing of each block alone does not provide it.

This is the remaining nonroutine operation: replace the sparse multiscale L2 argument by a bound using the q<3/2 vector-valued block estimate and preserving the critical dyadic weights. Neither a favorable result nor impossibility of this operation has been established here.

## 3. Paid alternatives and precise boundaries

Beltran–Roos–Seeger, A Note on Endpoint Bochner–Riesz Estimates, Theorem1.2 and its introduction, already provide the scalar epsilon-removal/vector-bump mechanism from strict fixed-radius hypotheses. Substituting source078 into that scalar operation is not a substantial discovery. Their input depends on a spatial cube index and does not directly supply the arbitrary radial Hilbert-space input above. No claim is made that it could not be adapted.

Lee–Seeger Theorem1.1 already proves a.e. convergence at critical order for L^{p,1}, every p>3, without the source. Their introduction explicitly separates this from the global maximal Lp norm. Thus proving convergence again is not a fallback target. LRS Corollary1.3 already proves the desired maximal endpoint for p>4; this range must be credited, not counted again.

The prohibited stronger Lp-input endpoint fails already for one radius. Indeed K_delta has outgoing phase with size |x|^(-2-delta). At delta=1-3/p, an input on 1<|x|<R with conjugate outgoing phase and amplitude |x|^(-3/p) has Lp norm O((log R)^(1/p)), whereas its fixed-radius output on a sufficiently small fixed ball is of order log R (the opposite phase contributes bounded oscillatory error). The L^{p,1} norm is of order log R, so this obstruction does not refute our actual target. The oscillation and angular factor are handled by choosing the ball small enough that the angular integral has positive real part. This is a classical kernel necessity calculation, not a nomination.

## 4. A bounded part of the sparse endpoint argument does close

Here is more than a failure of summation: the source estimate pays the entire short-radius portion of the restricted-weak argument in the new exponent range. This is a supporting deduction, not the full target.

Fix 1<q<r0<3/2 and c>0. Work with LRS's compactly supported smoothing kernels psi and eta, their unit-cube atoms b_(j,z,t), and finite index sets E_j. Each atom has pointwise H/L1(dnu) norm at most one and spatial support in the unit cube q_z. Define V_(j,z) exactly as there, and V_j=sum_(z in E_j) V_(j,z). The single-block bound derived above, extended over the non-annular frequency tails by the smooth cutoff decay and its vanishing moments (alternatively restricted to a fixed annular model), would give

 ||V_j||_(r0)^(r0) <= C_(r0,epsilon) 2^(j(3+epsilon*r0)) #E_j.

For the fixed annular model this bound follows directly from the preceding source estimate: disjoint unit-cube supports imply ||sum_z b_(j,z,t)||_{Lr0(H)}^(r0)<=#E_j, also with the L1(dnu) norm by Minkowski and the atom normalization. No sparsity condition on E_j is needed. The assertion for the complete psi/eta operator is explicitly conditional on the tail extension just described; it is not silently identified with the annular model.

Set J=floor(c log2 lambda), lambda>=2. For the annular model, triangle in Lr0 followed by Holder over the J indices gives

 ||sum_(1<=j<=J) V_j||_(r0)^(r0)
 <= C J^(r0-1) lambda^(c*epsilon*r0) sum_(j<=J) 2^(3j)#E_j.

Choose epsilon=(r0-q)/(2*c*r0). Chebyshev then bounds the level-lambda measure by

 C (log lambda)^(r0-1) lambda^(-(r0+q)/2) sum_j 2^(3j)#E_j
 <= C_(q,r0,c) lambda^(-q) sum_j 2^(3j)#E_j.

Thus the epsilon loss can genuinely be absorbed below the logarithmic radius cutoff, using a strict exponent r0 between q and 3/2. This does NOT solve the large-j portion. For j>c log2 lambda, its factor 2^(epsilon*j*r0) is unbounded in lambda, and the old L2 diagonal argument still yields only q<4/3. A successful full proof must control that long-radius sparse diagonal by a new estimate with constants uniform in j; controlling only cross terms or only short radii is insufficient. The annular-model limitation and the additional low-frequency-tail obligation are retained.
