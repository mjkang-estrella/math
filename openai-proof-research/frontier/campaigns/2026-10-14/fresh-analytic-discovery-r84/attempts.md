# Two nonroutine continuations tested; no target frozen

## A. Heteronuclear stability

Prospective full target considered: an actual three-electron two-nucleus Coulomb molecule with unequal positive integer charges whose spin-summed absolute-ground-state density is not representable by a common scalar potential in L^{3/2}+L∞. The symmetric source molecule is not itself such an example. No full scope has yet been frozen.

Analytic perturbation of the isolated many-electron eigenstate would preserve local density and spectral information for sufficiently small relative charge asymmetry. Taking adjacent large integer charges could make that relative perturbation arbitrarily small. This does not preserve the decisive exterior hypothesis: source05 uses g=√n exactly on z=0, because its constrained minimizing angle is odd and vanishes on that reflection plane. Unequal charges remove that reflection. The direct removal channel's zero surface and the minimizing angle's zero surface are distinct unknown objects. Closeness on every fixed compact set supplies no bound at arbitrarily large radius or on the shrinking transition layer.

Thus the missing estimate is not just a perturbation radius for eigenvalues. One must construct the nonsymmetric ensemble certificate with both orbital normalization and orthogonality constraints, identify its zero hypersurface, and prove a sufficiently slow density trace on that SAME hypersurface, uniformly at infinity. A sign-changing leading removal amplitude would alone not identify this hypersurface. Nothing in the read source interfaces establishes this. No statement of robustness or heteronuclear nonrepresentability is claimed.

## B. Determine the singular limiting potential rather than perturb symmetry

A plausible genuinely new operation would identify the asymptotic concentration of the source's uniquely relevant formal potential V near its median plane, beyond mere nonmembership in a function space. The tempting attractive delta-layer ansatz is not established by the source's density translation limits.

For an illustrative one-dimensional model, put g_epsilon(z)=exp(-a sqrt(z²+epsilon²)), a>0. Direct differentiation gives

V_epsilon=g_epsilon''/(2g_epsilon)=a² z²/[2(z²+epsilon²)] - a epsilon²/[2(z²+epsilon²)^{3/2}].

Against compact smooth tests, the first term tends to a²/2 and the second to -a delta_0: substitute z=epsilon*s and use int(1+s²)^(-3/2) ds=2. The attractive term has Lp norm of order epsilon^{1/p-1} for p>1. This is an exact classical thin-layer model, not the molecular potential. Adding a tangential exponential e^{-kx} would add k²/2 to its formal potential locally.

The source has a planar density floor of order A(r)² r^{-8} and a fixed-window leading profile (A(r)/r)² z², suggesting a crossover width of order r^{-3}. But neither scale comparison specifies the subleading positive orbital g away from the plane. Its angle equation is a nonlinear weighted PDE, and the source's conclusion that angle→pi/2 in translated off-plane windows is proved UNDER the contradictory assumption V in L^{3/2}+L∞. It cannot be reused as an unconditional asymptotic fact to derive a delta limit.

The proposed boundary-layer route would need a new unconditional normalized angle/orbital compactness theorem at the shrinking crossover scale, control of tangential derivatives, matching to the outer solution, and a uniform-integrability estimate for V as a signed measure. The source's fixed-window density convergence and lower planar tail do not give these. Even a pointwise ansatz for g can produce different positive ridges and negative wells while keeping the same plane/off-plane exponential rates.

This is already visible in the actual Gori-Giorgi–Gál–Baerends primary, arXiv1109.2204v2 Section V.B: its analytical models choose different angular switching functions and obtain different asymptotically singular potentials, warning that all occupied orbitals must still reproduce the same density. Their models are antecedents for the spike mechanism, not proofs of our proposed molecular limit. No specific delta coefficient or even finite signed-measure convergence is claimed for the source molecule.

The separate form-domain.md closes the canonical generalized representation exactly, but that is a routine classical completion of the source's certificate and is explicitly excluded from nomination. Neither that supporting consequence nor the one-dimensional delta model substitutes for A or B.

## C. A quantitative failure of the proposed density-to-potential transfer

This calculation isolates the derivative information missing in B; it is not a molecular counterexample or a nominee. Fix a>0 and a nonzero even smooth compactly supported psi with psi(0)=0. Set

 u_e(z)=-a sqrt(z²+e²), g_e=exp(u_e), and gtilde_e=g_e exp(sqrt(e) psi(z/e)).

Then gtilde_e/g_e→1 uniformly, and gtilde_e(0)=g_e(0) exactly. Outside a shrinking interval the orbitals agree exactly. Nevertheless their potentials have different distributional limits. Since V=(u''+(u')²)/2,

 Vtilde_e−V_e = (1/2)e^(-3/2)psi''(z/e) + e^(-1/2)u_e'(z)psi'(z/e) + (1/2)e^(-1)(psi'(z/e))².

The first term tends to zero as a distribution: it is half the second derivative of sqrt(e)psi(z/e), whose L1 norm is O(e^(3/2)). The second has L1 norm at most a sqrt(e)||psi'||_1, hence tends to zero. Substitution in the last term gives the positive measure limit (||psi'||_2²/2)delta_0. Thus

 Vtilde_e → a²/2 + (-a+||psi'||_2²/2)delta_0

in distributions, while V_e→a²/2−a delta_0. Multiplying psi by a constant varies the extra coefficient arbitrarily over nonnegative values without changing any of the uniform orbital-ratio or exact-plane conclusions. The first term's total variation typically diverges, so this is deliberately a distributional statement, not weak convergence of finite signed measures with uniformly bounded variation.

Consequently even uniform relative orbital control and exact plane values would not justify the sought potential-layer coefficient. The actual source offers less than this for g on shrinking windows. A successful route must exploit its nonlinear angle PDE to control the scaled log-gradient energy and second derivatives; fixed-window density asymptotics alone cannot supply that control. These artificial pairs do not satisfy the source angle PDE, normalization constraints, or common two-orbital eigen-equations, and therefore do not refute the prospective molecular assertion.
