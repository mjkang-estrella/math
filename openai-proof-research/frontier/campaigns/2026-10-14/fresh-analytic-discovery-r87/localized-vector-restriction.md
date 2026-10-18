# A localized vector restriction estimate from source079

Author supporting deduction only. Full target remains the r85 critical maximal theorem, including every3<p<=4. This lemma does not assert cross-scale summation or a favorable contribution verdict.

Fix1<q<3/2 and epsilon>0. For every L>=2, every finite family of numbers t_k in[1,2], and complex functions a_k supported in one cube of side L in R³,

 ||(sum_k |ahat_k(t_k omega)|²)^(1/2)||_{Lq(S²)}
 <= C_(q,epsilon) L^epsilon ||(sum_k |a_k|²)^(1/2)||_{Lq(R³)}.       (VR_L)

Fourier convention is exp(-ix.xi). Replacing t_k by -t_k or the sign in the transform is immaterial. Constants are independent of the number and positions of the t_k. We prove the positive-sign version below. Translation of the common support cube only multiplies each component by a modulus-one factor, so assume its center is zero.

## 1. Exact smoothed spherical operator and the source estimate

Choose a fixed real radial C_c^infinity multiplier p, equal one on {1<=|xi|<=2}, supported in {1/2<|xi|<3}. Write P=p(D) and kappa=F^{-1}p. This annular P is retained throughout; no assertion that P preserves physical support is made. Let sigma_r denote ordinary surface measure on the radius-r sphere. In dimension three its transform is4pi r sin(r|xi|)/|xi|. Therefore

 B_S F = integral_S^{2S} P(sigma_r*F(r,.))dr

is a fixed linear combination of integral r exp(±ir|D|) [p(D)/|D|]F(r,.)dr. Source079's displayed full strict local smoothing, scaling, Holder in the normalized time variable, and duality give

 ||B_S F||_q <= C_(q,eta) S^(3/q+eta) ||F||_{Lq_z L2([S,2S],dr/r)}     (1)

for every eta>0. The multiplier p/|xi| is smooth and annular, so introduces a uniform Lp bound. For clarity: if p_dual=q/(q-1)>3, source smoothing gives S^(1-3/p_dual+eta) for exp(ir|D|) on Lp_dual_x L2(dr/r). The adjoint of integration against r dr, expressed with dr/r, has factor r². Thus2+1-3/p_dual=3/q. This establishes(1) for both signs with the exact spherical kernel; no extension to non-annular frequencies is used.

## 2. Cutoff and far-field error, with P tails retained

Take chi in C_c^infinity((1,2)), equal one on[5/4,7/4]. Let S=C0 L^4 with a sufficiently large fixed C0. For each k put F_k(r,z)=chi(r/S) exp(-it_k r)a_k(z). Before applying P, the coarea identity is exact:

 integral_S^{2S} (sigma_r*F_k(r,.))(x)dr
 = integral a_k(z) chi(|x-z|/S) exp(-it_k|x-z|)dz.                 (2)

For x=rho omega with11S/8<=rho<=13S/8, define

 M_k(x)=exp(-it_k rho) integral a_k(z) exp(it_k omega.z)dz.

The output of(2) after P is the integral in z,w with the extra factor kappa(w) and x replaced by x-w. For |w|<=S/16 and z in the input cube, C0 ensures |z+w|<=rho/2 and |x-z-w|/S lies in[5/4,7/4]. Hence chi=1 and

 ||x-z-w| - rho + omega.(z+w)| <= C |z+w|²/S.

Since1<=t_k<=2, the corresponding exponential error is at most C(|z|²+|w|²)/S. Integrating the absolute value against |kappa(w)| uses its finite second moment. On |w|>S/16 both the actual and approximating phase/cutoff factors are bounded, and the Schwartz tail contributes O_N(S^(-N)). Finally,

 integral kappa(w) exp(it_k omega.w)dw = p(t_k omega)=1.

Minkowski in the finite-dimensional ell2 space therefore gives the uniform vector error

 (sum_k |B_S F_k(x)-M_k(x)|²)^(1/2)
 <= C (L²/S+S^(-N)) integral (sum_k|a_k(z)|²)^(1/2)dz
 <= C L²/S ||A||_1,                                             (3)

where A(z)=(sum|a_k(z)|²)^(1/2), L>=2, and N can be fixed large. This bound handles P's noncompact physical convolution explicitly. The original functions a_k, not P a_k, have common compact support.

## 3. Randomization and the q<2 inequalities

Let epsilon_k be independent Rademacher signs, and F=sum_k epsilon_k F_k. For each z, concavity of u^(q/2), followed by Tonelli and E|sum epsilon_k c_k|²=sum|c_k|², gives

 E ||F||_{Lq_z H}^q
 = integral E (integral |chi(r/S)|² |sum epsilon_k exp(-it_k r)a_k(z)|² dr/r)^(q/2) dz
 <= integral (integral |chi(r/S)|² A(z)² dr/r)^(q/2) dz
 = C_chi^q ||A||_q^q.                                           (4)

Apply(1) and take expectations. On the output, the lower Khintchine inequality for complex coefficients gives

 E ||B_S F||_q^q >= c_q integral (sum_k|B_S F_k(x)|²)^(q/2)dx.      (5)

There is no interchange of an Lq and L2 norm in the wrong direction. Equations(4),(5) are the only probabilistic norm comparisons used.

For every point of the interior shell, the ell2 norm of(M_k(x)) is precisely

 R_A(omega)=(sum_k |integral a_k(z)exp(it_k omega.z)dz|²)^(1/2),

independent of rho. The shell volume element is rho² drho d sigma(omega), and its radial integral is a fixed positive multiple of S³. Using(3), the triangle inequality in Lq, and(4),(5) yields

 ||R_A||_{Lq(S²)} <= C_(q,eta) S^eta ||A||_q + C L²/S ||A||_1.     (6)

The input support has volume L³, so ||A||_1<=L^(3-3/q)||A||_q. With S=C0 L^4 the error coefficient is at most C L^(1-3/q), which is bounded for q<3/2. Set eta=epsilon/4. Then S^eta=C0^eta L^epsilon and(6) proves(VR_L).

Smooth compactly supported a_k suffice initially. General Lq functions in the cube follow by Lq approximation, since the finite-volume support also gives L1 convergence and uniform convergence of each Fourier transform. This proof claims only finite families; a continuum-frequency extension would require its own simple-function limiting argument and is not needed for(VR_L).

## 4. What this does and does not change

The radius S is chosen from the support diameter L, rather than from the eventual very long propagation radius. Thus the loss is L^epsilon, not R^epsilon. This is a genuine quantitative improvement for clustered inputs when R is much larger than L. It supplies a possible replacement for local cluster estimates in a long-radius decomposition.

It does not establish an R-bounded restriction estimate without a support-size loss, the complete radial Hilbert-valued far-field reconstruction for arbitrary F(r,z), or a bound on the deterministic sum of outputs from many distant clusters. Those are separate obligations. No Lq(H)->L2 bound beyond4/3 is asserted. The old p>4 maximal endpoint and all-p>3 a.e. convergence remain credited antecedents.
