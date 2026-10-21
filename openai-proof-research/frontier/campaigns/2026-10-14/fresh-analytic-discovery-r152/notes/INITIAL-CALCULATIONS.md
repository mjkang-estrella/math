# Initial conditioning and what it actually pays (prefreeze)

Notation: epsilon>0, mu=epsilon^-2, n=floor(mu), f0 as H ass:kinetic, rho0=int f0 dv, b=(4pi/3)||rho0||infinity epsilon^3. The canonical probability is Z_n^-1 1_Dn product f0 dz. It is exactly the grand-canonical law conditional on N=n; the activity cancels. All calculations below are source/classical compositions, not a nominated result.

## Number local limit from H02's convergent Mayer series

Write log Z(lambda)=sum_{k>=1} a_k lambda^k with a1=1 and |a_k| <= k^(k-2)b^(k-1)/k! for k>=2, by H eq:initial-unrooted-tree-integral. For lambda in [mu/2,2mu], every fixed derivative satisfies sum_{k>=2}k^r |a_k|lambda^k <= C_r lambda^2 b=O_r(mu epsilon). For real lambda, a_k is real. The characteristic function of N obeys

  log |E_lambda exp(i theta N)| = sum_k a_k lambda^k(cos(k theta)-1).

Use 1-cos(k theta)<=k^2(1-cos theta). The k>=2 contribution is at most C lambda^2 b(1-cos theta), while the first is -lambda(1-cos theta). Hence for sufficiently small epsilon,

  |E_lambda exp(i theta N)| <= exp[-c lambda(1-cos theta)], |theta|<=pi.

This is a genuine whole-circle bound for the NUMBER variable, obtained from the initial partition function; no dynamic observable is inserted. Let m=E_mu N, sigma²=Var_mu N. Then m=mu+O(mu epsilon), sigma²=mu(1+O(epsilon)), and the centered logarithm at theta=u/sqrt(mu) is -u²/2+o(1), by the third-derivative bound O(mu). Fourier inversion and the whole-circle majorant give

  sqrt(mu) P_mu(N=n) -> (2pi)^(-1/2) exp(-a²/2)

whenever (n-m)/sqrt(mu)->a. For n=floor(mu), H's first Mayer correction gives

  m=mu-mu² int 1_{|x-y|<=epsilon}rho0(x)rho0(y) dxdy+O(mu epsilon²),
  (n-m)/sqrt(mu) -> a0=(4pi/3)int rho0² dx.

The spatial-gradient bound gives an O(epsilon^4) error in the integral; both resulting errors after division by sqrt(mu) tend to zero. Thus P(N=n)~epsilon (2pi)^(-1/2)e^(-a0²/2). This pays exact conditioning probability, not conditioned dynamics.

## Scalar canonical partition expansion already pays initial CLT

For one fixed bounded real test phi, m(u)=int f0 e^(u phi). On a fixed complex disk about 0, m(u) is bounded away from 0 and p_u=f0 e^(u phi)/m(u) satisfies |p_u|<=C f0 and int|p_u|<=C. For a physical exclusion polymer V of k labels, define its weight w_u(V)=int U_k product p_u. H's tree inequality gives |w_u(V)|<=C^k k^(k-2)b^(k-1). The finite canonical partition is the hard-core polymer partition over disjoint subsets of [n]. For each label i,

  sum_{V contains i} |w_u(V)|e^(a|V|) <= C n b=O(epsilon).

Indeed the size-k sum is bounded by binom(n-1,k-1) C^k k^(k-2)b^(k-1)e^(ak), a convergent geometric series after Stirling for nb small. The classical polymer convergence criterion read in PT1105.1022v4 §4 and PT1409.2718v3 §3 now yields an analytic branch R_n(u)=log Z_n[p_u] with |R_n(u)|<=C n² b=O(n epsilon) on a smaller fixed disk. This extends the existing leaf-integration proof to the inhomogeneous probability base: no translation invariance is used in this scalar bound. Complex normalization is controlled by |p_u|<=C f0. The underlying abstract cluster theorem is credited, not re-proved here.

Therefore the exact identity

  log E_can exp(u sum_i phi(z_i)) = n log m(u)+R_n(u)-R_n(0)

and Cauchy bounds imply kappa_k(sum phi)=n kappa_k(phi(Z))+O_k(n epsilon) for each fixed k. Exact centering and division by sqrt(n) yield initial Gaussian moments and the multivariate covariance int f0 phi psi - (int f0 phi)(int f0 psi). Moment determinacy proves the initial finite-dimensional CLT. No finite-time theorem follows just from this scalar integrated estimate.

## Direct cutoff-conditioning loss

H05 gives P_GC(E_bad)<=C epsilon^(1+eta), eta=1/20 (full H05 proof subsequently read before final synthesis). The number local limit gives P_can(E_bad)<=C epsilon^eta. Thus true/pasted UNcentered finite vectors coincide with probability tending to one under canonical conditioning. But the elementary exact-centering estimate is

  |E_can(S_true-S_pasted)|/sqrt(mu)
  <= 2||phi||infinity n/sqrt(mu) P_can(E_bad)
  <= C epsilon^(eta-1),

which is not useful. This does not show the actual expectation difference diverges; it shows that this particular bound does not close centering. A direct canonical witness expansion with P_can(E_bad)=o(epsilon), or suitable conditioned uniform integrability of centered fields plus a proved centered comparison, would repair it. Source GC moment bounds cannot simply be divided by P(N=n) without tracking this loss.

## Fourier conditioning is stronger than an initial local limit

For S=sum_j theta_j sum_i phi_j(z_i(t_j)), the canonical characteristic function is the coefficient ratio

  int_{-pi}^{pi} e^(-i n theta) E_GC[e^(i S/sqrt(mu)) e^(i theta N)] dtheta / (2pi P_GC(N=n)),

with the chosen exact centering applied separately. H supplies fixed-order marked cumulants; these alone do not give an integrable majorant for this mixed whole-circle transform after division by epsilon. BGSS has factorial-in-order cumulant bounds and a generating function at SHORT times. Its proof and the regular-lifespan H proof have different order dependence. The scalar number bound above does not dominate the mixed transform: multiplying by a unit-modulus path functional can destroy number-frequency cancellation.
