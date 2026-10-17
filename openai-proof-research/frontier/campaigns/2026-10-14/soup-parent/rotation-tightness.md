# Uniform path tightness by Gaussian rotation

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.
Supporting standard Gaussian argument, not a full SOUP solution.

For p>=1 write m_p=E|G_1|^p for a standard scalar Gaussian. If f is a
smooth L-Lipschitz function on Euclidean space, and G,H are independent
standard Gaussian vectors, put G_u=cos(u)G+sin(u)H. Its derivative
V_u=-sin(u)G+cos(u)H is a standard Gaussian vector independent of G_u.
Thus conditionally on G_u, grad f(G_u).V_u is centered Gaussian with
variance |grad f(G_u)|^2<=L^2. Minkowski's integral inequality gives

    ||f(G_theta)-f(G)||_p <= theta m_p^(1/p) L,  0<=theta<=pi/2.

This is dimension free. For a correlated standard Gaussian pair with
covariance rho I, 0<=rho<=1, take theta=arccos(rho). Concavity of sine
on [0,pi/2] gives sin(theta/2)>=theta/pi, hence

    theta^2 <= (pi^2/2)(1-rho).

For the SK function in SOUP, each derivative has absolute value at most
beta/sqrt(n); there are n(n-1)/2 edges. Thus L^2<=beta^2(n-1)/2.
For the OU observations at rescaled times s,t, rho=exp(-|t-s|n^(-2/3)).
The centered rescaled increments therefore satisfy

    ||Z_n(t)-Z_n(s)||_p
      <= (beta*pi/2) m_p^(1/p) sqrt(|t-s|),

because n^(-1/3)(n-1)n^(-2/3)<=1 and 1-exp(-u)<=u.
This holds for every n>=2 and all real s,t. The centering cancels from
the increment. All paths are continuous since F is smooth and the finite
OU vector has continuous paths.

The source one-point moment theorem supplies uniformly bounded pth moments
at time zero, after removal of its independent Gaussian completion. Apply
the usual Kolmogorov tightness criterion on each compact interval with
p>2. Any Holder exponent strictly below 1/2-1/p is available in the
criterion; choose p arbitrarily large to obtain compact-uniform tightness
and subsequential laws supported on locally alpha-Holder paths for every
alpha<1/2. A diagonal choice over integer compact intervals gives tightness
on C(R). Stationarity and reversibility pass through finite-dimensional
convergence. Every subsequential law has the prescribed source marginal
sqrt(a2(beta))*nu_beta and mean zero.

These conclusions DO NOT prove uniqueness of the subsequential law or
that it moves in time. A temporally constant process with the same marginal
satisfies all those conclusions. Both full-sequence convergence and
nonconstancy remain mandatory in the original SOUP target.
