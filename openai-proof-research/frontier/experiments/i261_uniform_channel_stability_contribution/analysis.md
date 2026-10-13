# Contribution analysis: I262

Verdict: **TECHNICAL**, contribution gate only. The target and all restrictions are specified in the review. All pinned results are stipulated true.

## Independently derived same-exponent tail bound

Let p=gamma+1/2 in (1,2), M=||f||_infinity, kappa_profile=w0^(1/r)/c², and U=B_w w ff^T. Its only nonzero pointwise eigenvalue is B_w w |f|². Thus

    tr(U^p)=B_w^p w^p |f|^(2p),
    integral tr(U^p)<=B_w^p M^(2p) integral w^p<infinity.

The pinned matrix main theorem applies to U in dimension m-1, including dimension one. With I262's compressed form comparison, interlacing orders the j-th eigenvalue of K_f below the (j+1)-st eigenvalue of H whenever the latter is negative. This gives for every finite initial tail sum, then by monotone exhaustion,

    S<=Tr(K_f)_-^gamma<=C_gamma B_w^p integral w^p |f|^(2p).

The profile relation is exact: rho=c² sech^(2/r)(ra x)=c²(w/w0)^(1/r), while p=1+1/r. Therefore

    integral w^p |f|²=kappa_profile T,
    |f|^(2p)<=M^(2p-2)|f|²,
    S<=N_LT M^(2gamma-1)T,
    N_LT=C_gamma B_w^p kappa_profile>0.

This derivation has no eigenvalue-count factor, support constant, derivative norm or pointwise coordinate sum. It does not require HLW's endpoint. It remains valid for an infinite tail by exhaustion. For M=0 both sides vanish; for gamma>1/2 the error-to-T ratio tends to zero. The same deduction would work with any already available dimension-uniform matrix LT constant at gamma; sharpness is not required for the effective potential estimate, although the stipulated equality value is needed for the original deficit normalization.

## Exact alternate closure, conditional on the other proposed lemmas

Retain I262's centering T=J, V>=(1-M^4)T, Q>=T/[2(r+2)], and |delta-Q|<=A0 M²T. Retain 0<=delta<=T and delta<=a²/8. The mean-value estimate gives

    D>=m_gamma delta-S
      >=[m_gamma/(2(r+2))-m_gamma A0 M²-N_LT M^(2gamma-1)]T,
    D<=M_gamma delta<=M_gamma T.

Choose

    M_LT=min{rho0/2,1/2,
             [1/(8 A0(r+2))]^(1/2),
             [m_gamma/(8 N_LT(r+2))]^(1/(2gamma-1))},
    eta_LT=min{1/8,M_LT/4}.

Then the two errors are at most m_gamma T/[8(r+2)] each. Hence D>=m_gamma T/[4(r+2)] and D<=M_gamma T. This is the same qualitative theorem, with explicit constants independent of support and m, and a potentially different amplitude radius. It is not a validation of I262's original displayed eta or of its analytic remainder proof.

## What endpoint interpolation adds

HLW applied to U gives S<=[(B_w/2) integral w|f|²]^(2gamma). Hölder on the measure |f|² dx, with exponents 2gamma and 2gamma/(2gamma-1), uses

    1=p/(2gamma)+(1/2)(1-1/(2gamma)).

It yields

    (integral w|f|²)^(2gamma)
       <=(integral w^p|f|²)(integral sqrt(w)|f|²)^(2gamma-1)
       <=kappa_profile T (M² I_w)^(2gamma-1).

This recovers I262's N0 M^(4gamma-2)T. It is sharper in amplitude order than the direct estimate for each fixed open-range gamma. Its finiteness and independence of m and support are clear. Nevertheless both positive exponents already close the stated theorem. At gamma approaching 1/2 neither route gives an amplitude threshold uniform in gamma, and no endpoint result follows.

## Why the remaining assembly is local perturbation theory

The covariance maximizer gives exactly J=Z(1-lambda_max). Its orthogonality condition cancels the chart's linear mean; |1-sqrt(1-|f|²)|<=|f|² for M<=1/2 gives the M^4T mean-error estimate. This is a finite-dimensional centering procedure with Hilbert norm bounds, so no channel factor is introduced.

For global coercivity, the source's partner operator is L_+=-d²+[(r-1)/(r+1)]w. Its positive potential and y=(AA*)^(-1)Au give

    q_h[u]>=a² ||y'||²+a²[(r-1)/(r+1)] integral w|y|²,
    integral w|A*y|²<=2w0||y'||²+2a² integral w|y|².

The displayed c_w follows by adding the two resulting coefficients. This is a useful estimate, but an elementary consequence of the existing explicit factorization; no positive unweighted gap for h on phi-perp is asserted. Completing squares produces the scalar free-resolvent quadratic form; summing its components preserves constants. An isolated simple eigenvalue and operator-norm smallness then put the remaining local estimate in the familiar coercive-second-variation plus controlled-remainder framework.

The new-to-project result is a carefully assembled transverse stability corollary. The concrete same-exponent route shows why its full-sum and support-free description alone is insufficient to demonstrate a nonroutine substantial increment. This conclusion does not rely on assuming an unproved vector version of a scalar stability theorem, or on a negative literature search.
