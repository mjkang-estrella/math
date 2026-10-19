# Source078: smooth phase versus the actual Gevrey interface

This is prefreeze feasibility, not a candidate declaration. The constants below may depend on the fixed smooth phase, its compact slope domain, ellipticity, fixed support and the requested positive loss. There is no uniform bound over all smooth functions with only a C2 bound, no critical endpoint, and no maximal-operator assertion.

The exact pinned input is `thm:oscillatory-estimate` in `12-multiplier.tex`: for a two-dimensional input and three-dimensional output, the L3 estimate has decay lambda^(-1+nu), for every nu>0. Its derivative identity is partial_v Phi= zeta(v,x-cv), with symmetric uniformly definite partial_p zeta and fixed Gevrey Hessian bounds. The rest of that file actually performs the radial slicing, pseudoconformal substitution, globally definite Hessian extension, spatial binning, shell expansion and strict-order interpolation. These are stipulated operations, not new constructions to claim here.

Consider a fixed smooth function g on a neighborhood of a compact slope patch, with positive definite Hessian bounded above and below. Work with a smooth compactly supported convolution phase

    h(y',t)=t g(y'/t),       0<c<=t<=C.

Negative definite Hessians are handled by the permitted sign convention, but no sign variant is a separate candidate. The exploratory question was whether a merely smooth g leaves a genuine obstruction to the source's Gevrey phase contract.

Fix small epsilon>0 and let rho=lambda^(-epsilon). Partition the compact slope set into O(rho^(-2)) caps. For a cap center q0 and a fixed input third coordinate y3, divide y' into squares of side rho. Write

    y'=y0+rho v,   z'=y0+t q0+rho X,   t=z3-y3,
    Lambda=lambda rho^2.

The support for a cap forces X,v into fixed bounded sets (enlarging bins a bounded number of times). At each fixed t, output bins have bounded overlap. Taylor's affine terms separate into input and output factors of modulus one. The remaining phase is

    Lambda t G_rho((X-v)/t),
    G_rho(q)=[g(q0+rho q)-g(q0)-rho grad g(q0).q]/rho^2.

Let P_rho be its Taylor polynomial of degree N at zero. On every fixed relevant q ball,

    ||G_rho-P_rho||_(C^j) <= C_(j,N,g) rho^(N-1)

for each fixed j. For j<=N+1 this is Taylor's remainder with derivatives; for j>N+1 the polynomial derivative vanishes and rho^(j-2)<=rho^(N-1). Choose N with epsilon(N+1)>=1. Then Lambda(G_rho-P_rho), including all derivatives required of the fixed smooth amplitude, is bounded independently of lambda and q0. Thus exp(i Lambda t(G_rho-P_rho)) belongs in that amplitude. This is a derivative estimate for the whole residual factor; merely bounding its value would not suffice.

The quadratic part Q of P_rho has the original uniformly positive Hessian. On a fixed larger ball the remaining polynomial has C2 size O(rho). Extend by

    Q + chi(P_rho-Q),

where chi is a fixed compactly supported Gevrey cutoff equal to one on that ball. For sufficiently small rho its Hessian remains uniformly positive everywhere. Because N is fixed after epsilon, its higher derivatives have one uniform Gevrey envelope, depending on N and g but not lambda or q0. The finitely bounded remaining lambda range is controlled directly. This avoids assuming a global smooth convex extension of the original g with uniform Gevrey derivatives.

Set s=1/t and Z=X/t. The phase becomes s^(-1)P_rho(Z-sv). Differentiating in v yields -grad P_rho(Z-sv). An affine normalization of the compact s interval gives the source x-cv form (a fixed v-dependent translation inside zeta is allowed). Jacobians are bounded on c<=t<=C. The source estimate at scale Lambda therefore applies to every bin, with uniform constants for this family of phases and amplitudes.

The input Jacobian contributes rho^2. The physical transverse L3 factor rho^(2/3) cancels the input rescaling rho^(-2/3). Thus a bin has norm bound

    C rho^2 Lambda^(-1+nu)
      = C lambda^(-1+nu) rho^(2nu).

Bounded overlap sums bins for each cap without an additional power of rho. Triangle inequality over O(rho^(-2)) caps gives

    C lambda^(-1+nu+2epsilon-2epsilon nu).

For any requested eta>0 choose positive epsilon,nu with 2epsilon+nu<eta, then choose N as above. Minkowski in the bounded y3 interval is the same source slicing step. The full smooth homogeneous phase calculation therefore fits a lambda^(-1+eta) strict-loss bound. None of the constants is independent of eta or the selected high derivatives of g.

The closest primary proof read was Guo–Oh–Wang–Wu–Zhang, *The Bochner–Riesz problem: an old approach revisited*, [2104.11188v1](https://arxiv.org/pdf/2104.11188v1): §2 performs slicing and pseudoconformal reduction; Lemma3.8 rescales the phase; Lemma3.10 uses a Taylor remainder as a uniformly smooth amplitude and Fourier expands that amplitude. Their exact theorem is not asserted to be this entire smooth phase statement. Their actual operations supply the relevant compatible compiler precedent, while the stronger pinned estimate supplies the exponent.

Chronology matters: the initial Taylor feasibility calculation preceded the full Lemma3.10 read. That primary comparison was completed before selection; no freeze occurred at any point. The all-strict-order multiplier shell summation is already a source operation, but this round does not present a complete new general-convex multiplier theorem or claim every stationary-phase interface was independently developed. A smooth-phase headline alone does not identify an unpaid integrated operation after the displayed reduction. General variable phases without this homogeneous difference structure, rough curvature, maximal and critical-order estimates are not consequences claimed here.
