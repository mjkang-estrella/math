# I260 derivation audit

Target: authenticated I262, SHA256 1899a85fadb07ed0dd34b1396c31033c80d7a8b88b45455cdcb4f5116931cbfb. Verdict: PASS, correctness only. The review file contains the full chain and source contracts; this file records additional domain and stress-case details. This is not a numerical experiment or executable research implementation.

## Scalar identities and domains

Put t=a tanh(ra x). Then t²-t'=a²-(r+1)a² sech²(ra x) and t²+t'=a²+(r-1)a² sech²(ra x). Thus A*A=h+a² and AA*=a²+L_+. A has H¹ domain; its kernel is the normalized phi. Since AA*>=a², its inverse is bounded and the range of A* is phi-perp. For u in H¹ intersect phi-perp, y=(AA*)^-1 Au is H² and A*y=u. The fourth-order expression is understood through forms:

    ||Au||²-a²||u||²
       =||(a²+L_+)y||²-a² <y,(a²+L_+)y>
       =a² <y,L_+y>+||L_+y||².

All coefficients of A and their needed derivatives are bounded. Approximation in these graph/form domains is legitimate. No derivative of the orientation enters this construction.

For a component F=phi g,

    ||F'||²+a²||F||²
       =integral rho|g'|²+integral w rho|g|².

This follows from phi''=(a²-w)phi and extends by closure. The transformed form domain is the image of H¹ under division by positive phi. Constant g corresponds to F=b phi in H¹. The resolvent minimizer for bounded f has F in H². Since w f phi decays at least as exp(-(2r+1)a|x|), convolution with the free kernel exp(-a|x-y|)/(2a) bounds F by a constant times exp(-a|x|). Thus g=F/phi is bounded in the tails if an explicit representative is wanted; the closure argument already suffices.

The normalized ground-state density has c²=ra Gamma(1/2+1/r)/(sqrt(pi) Gamma(1/r)). The beta-integral normalization uses integral sech^(2/r)(ra x) dx=sqrt(pi)Gamma(1/r)/(ra Gamma(1/2+1/r)). Also Z=2(r+1)a²/(r+2), though its explicit value is not needed in the I262 constants.

## Analytic perturbation details

At fixed x, put s=|b(x)|, alpha=sqrt(1-z²s²). In the span of the first coordinate and b, the multiplier U_z is

    w [[z²s², -z alpha b^T],[-z alpha b, -z² b b^T]].

For |z|<=rho0<1/2, |alpha|<=sqrt(1+|z|²) and the diagonal/off-diagonal operator norms give ||U_z||<=6w0|z|. Moreover

    U_z psi=(z²w s² phi, -z w alpha b phi),
    ||U_z psi||²<=w0 T(b) |z|² (1+2|z|²),

and the same estimate holds for U_z* psi. These sharper elementary bounds imply the proof's generous factor 6. No norm of a coordinate sum occurs.

The contour Neumann product is <=1/2. The compressed inverse bound is (3a²/4-a²/8)^-1=8/(5a²). With the proof's weaker bound 2/a² and factor 6 for the two coupling vectors, Feshbach yields 4+72(r+1)<=80(r+1). The circle lies in an analytic neighborhood because the smallness inequalities have slack. Thus Cauchy estimates at rho0, or a limit of circles approaching rho0, are justified.

The first perturbation sends psi only into the free transverse channels. The second diagonal perturbation has expectation T(b). Therefore the second-order coefficient is exactly T(b)-sum <w b_j phi,(-d²+a²)^-1 w b_j phi>=Q(b), including its minus sign.

For real M, spectral inclusion places all other spectral points above -a²/8, while the rank-one branch lies near -a². This identifies the lowest eigenvalue without confusing the fixed psi compression with the projection onto its perturbed eigenfunction.

## Compression and tail checks

The compression is to a fixed codimension-one Hilbert subspace, with form domain H¹ intersect that subspace. Its embedding has a closed, dense form domain within the subspace. The lower comparison operator is (h/2 on phi-perp) direct-sum K_f. The first summand is nonnegative. Codimension-one interlacing shifts the negative list by exactly one; the removed vector need not be the perturbed eigenvector. The moment bound follows with multiplicities and zero padding.

Although the proof allows an infinite list by monotone limits, in this fixed finite m setting H>=h I_m additionally bounds its number of negative eigenvalues by m. This observation is unnecessary, and using it in the moment sum with a factor m would spoil the desired uniformity. HLW avoids that factor.

Tail translation pressure is paid at two different stages. The branch error is proportional to the weighted T because both Feshbach coupling vectors contain phi. The threshold potential instead sees integral w|f|²; it cannot simply be replaced by T using a lower bound for rho. The exact identity w rho proportional to w^(gamma+1/2), and interpolation against sqrt(w), supply the replacement. For q=2gamma>1,

    (integral w|f|²)^q
      <=integral w^p|f|² (integral sqrt(w)|f|²)^(q-1).

No compact minimum, tail cutoff, or support length appears. For a translated localized disturbance, the weights decay at different rates, but this global inequality still bounds every threshold contribution by N0 M^(q*2-2)T. Principal centering may introduce a small constant chart offset outside the original disturbance; neither the forms nor the interpolation require compact support, so that does not invalidate the argument.

## Decision

All claimed inequalities hold with the proposed constants, in the stated order. No required repair was identified. Optional expansions of form-domain notation and min-max directions are recorded in the review. Endpoints, complex fields, variable scalar profiles and multiple occupied channels remain outside the claim. Scalar and possible vector/matrix prior art remain for contribution review; no acceptance count is changed here.
