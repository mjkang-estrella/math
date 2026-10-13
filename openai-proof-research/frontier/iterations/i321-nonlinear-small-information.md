# I321 — nonlinear small-information endpoint

2026-10-13. **Full S313 remains UNRESOLVED; no exactly normalized counterexample is found.** The new proved partial T321 gives weighted nonlinear stability in a conditional-coordinate tube, with fixed interior bias and original endpoint spikes allowed. I320's finite-cube quartic normal form passes an independent analytic audit. Fourteen accepted findings remain unchanged toward twenty.

The full target retains every finite n, arbitrary u:{-1,1}^n->[-1,1] with exactly I(u)=psi(a), 0<a<=a1<1, and r in [r0,r1] inside (0,1). With Delta_r=psi(ra)-I(T_ru) and d_a=min_(i,s)E|u-s aX_i|², it asks for d_a<=C(a1,r0,r1)a^(-4)Delta_r. Arbitrary bias, means approaching endpoints, rare events and unrestricted complexity have not been removed from that question.

The [complete analysis](../experiments/i321_nonlinear_small_information/analysis.md) verifies I320's square completion and exact implicit normalization. For fixed finite dimension and interior m, h=1-m², Ef²=h, and g orthogonal to levels zero and one, its unique optimal quadratic correction is -(m/h)(f²-h). The optimized exactly normalized quartic coefficient is indeed

    r²(1-r²)[kappa*m²/(3h)+(1-kappa)/6],
    kappa=sum_i c_i^4/h².

This coefficient is positive except at a balanced signed coordinate. It does not justify a uniform normal-form reduction. At m²>1/3 spreading can lower the coefficient relative to a biased coordinate; that channel cannot be treated as a transverse local maximizer.

**New proved T321.** Fix additionally any m0<1. Write v=E[u|X_i]=m+bX_i after orientation, w=u-v, and delta=||w||_2. Define

    theta=1/(1+r1²)-1/2,
    qout=min{3,1+r1^(-2)},
    Mtube=max{2+1/(2theta),2/(qout-2)}.

There are a_*,epsilon_*,c_*>0 depending only on m0,a1,r0,r1 such that, if 0<a<=a_*, |m|<=m0 and delta<=epsilon_*a^Mtube, then

    Delta_r(u)>=c_*[a^4 m²
                     +a² sum_(j!=i) what(j)²
                     +sum_(|S|>=2) what(S)²].

Consequently the full endpoint inequality holds in this explicitly restricted tube. Its radius exponent is half of L313's conservative exponent; its mean need not shrink toward zero. A fixed-bias, exactly normalized nonlinear family with a dyadic rare event and exact endpoint +1 lies in this scope while remaining a fixed distance from every balanced-coordinate shrinking ball.

The proof uses an actual bounded one-bit conditional channel rather than an affine substitution. Its information amplitude beta is defined exactly by I(v)=psi(beta). The split I(u)=I(v)+E Bpsi(u,v) and concavity of J->psi(r psi^(-1)(J)) pay the input normalization at its exact secant. The residual Hessian has a two-by-two Walsh block whose Schur complement is

    2r²(1-r²)a²/[3(1-m²)]+O(a^4).

Other singleton modes therefore cost a² and higher modes cost order one. Global strong convexity keeps bad input spikes positive, and support hypercontractivity pays their noisy cross terms. The original kernel and its exact information are retained throughout. One-bit capacity is used only for the genuine v.

The unpaid operations remain exact: prove Delta_r>=c a^4[m²+q-max_i uhat(i)²+H] outside these conditional tubes, including a quantitative global entrance or direct alternative at vanishing a, and pay means approaching ±1 uniformly. A smoothed residual alone does not pay original higher mass. The Gaussian compact-rectangle proof has absolute errors, and I320 has no uniform representation/remainder theorem. Neither closes these operations.

Correctness and contribution are separate: the finite-cube audit and T321 are proved at their stated scopes; the unrestricted target is unresolved. T321 is a technical nonlinear partial, with no new substantial acceptance or worldwide-priority claim. Inherited B313, A313, L313 and I304 are not credited as new findings. [Reading/failures](../experiments/i321_nonlinear_small_information/reading-and-failures.md), [authentication](../experiments/i321_nonlinear_small_information/input-authentication.json), and [primary literature](../sources/i321_nonlinear_small_information/literature.md) record the boundary. Only the five assigned outputs are authored, with detached hashes at delivery.
