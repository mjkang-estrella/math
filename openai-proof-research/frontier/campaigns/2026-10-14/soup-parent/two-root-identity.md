# Exact finite two-root identity; no limiting closure

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; code MIT.
Parent derivation, not independent review or a substantial-result nomination.

Use the frozen SOUP normalization, n>=2, beta>1, N=n(n-1)/2.
Let F(g)=log sum_sigma exp(beta/sqrt(n) sum_{i<j} g_ij sigma_i sigma_j),
Y(g)=n^(-1/6)(F(g)-EF(g)). For tau>0 put rho=exp(-tau n^(-2/3))
and let (g,h) be standard Gaussian N-vectors with cross covariance rho I.
For arbitrary real q,r define M(tau)=E exp(qY(g)+rY(h)). Under the
probability tilt by this positive exponential divided by M, write E_tilt.
Conditional on g,h draw independent Gibbs spins sigma,eta and set
R=n^(-1) sum_i sigma_i eta_i. Then

    d/dtau log M(tau)
      = -(beta^2/2) q r rho E_tilt[ <R^2>_(g,h) - 1/n ].       (1)

The diagonal correction is essential for i<j couplings without completion.

Proof. Finite sums make F smooth, with partial_e F=(beta/sqrt(n))
<sigma_i sigma_j>. Its gradient is bounded. The exponential and all
derivatives used below have at most exponential-linear growth in |g|+|h|,
so Gaussian differentiation and integration by parts are justified on any
compact subinterval of rho in (-1,1). Differentiating covariance gives

    d/drho M = sum_e E[partial_ge partial_he exp(qY(g)+rY(h))]
             = qr n^(-1/3) E[exp(qY(g)+rY(h)) grad F(g).grad F(h)].

There is no 1/2: both symmetric cross blocks contribute to the covariance
derivative. Conditional Gibbs independence gives

    grad F(g).grad F(h)
      = (beta^2/n) sum_{i<j} <sigma_i sigma_j><eta_i eta_j>
      = (beta^2 n/2)(<R^2>-1/n).

Finally rho'=-n^(-2/3)rho. Dividing by M proves (1). The same formula
extends one-sided to tau=0 by continuity and Gaussian integrability.
No closure follows: the tilted overlap remains an unknown function of
n,tau,q,r. In particular the source one-point law only gives M(0).

Differentiating in q,r at zero yields, for C_n(tau)=E[Y(g)Y(h)],

    C_n'(tau)=-(beta^2/2)rho E[<R^2>-1/n].                    (2)

Thus E[(Y(h)-Y(g))^2] = beta^2 integral_0^tau exp(-s n^(-2/3))
E[<R_s^2>-1/n] ds. This identity does not by itself give a positive
limiting integral or full-sequence joint convergence.

Spectral boundary. With centered Hermite degree energies v_{n,k}>=0 of F,
C_n(tau)=sum_{k>=1} n^(-1/3)v_{n,k} exp(-tau k/n^(2/3)).
The measures mu_n=sum n^(-1/3)v_{n,k} delta_{k/n^(2/3)} have total mass
converging to a2 by the stipulated source moment theorem. The deterministic
gradient estimate gives integral lambda dmu_n = n^-1 E|grad F|^2
<= beta^2(n-1)/(2n). This bounds upper-tail mass, but does not prevent
all limiting mass sitting at zero. Even a positive first-moment lower
bound cannot prevent that without uniform integrability of lambda:
(a2-1/j)delta_(1/j)+(1/j)delta_j has mass a2 and first moment tending1,
while it converges weakly to a2 delta_0. This is a logical example of
spectral measures, not a counterexample within the actual SK model.

Source premise read directly: family217 limiting-law introduction,
thm:main and thm:moments, pinned fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
No source proof is being audited. Equations (1)-(2) above are finite
identities derived independently here; no correlated-root source theorem
is assumed. Full SOUP remains unresolved.
