# r168 prefreeze construction — reversible potential dynamics

No theorem is frozen or nominated. This is a concrete attempted operation beyond fixed-energy static universality, retaining the whole fixed-d, unconditioned graph ensemble. It is not a replacement for any older frozen scope. All formulas below use ordinary adjacency. The positive disorder w is fixed before n tends to infinity, at a value allowed by the Anderson source; there is no w_n -> 0 assertion.

## 1. An actual finite-n stationary process

Draw the simple d-regular graph uniformly, for every admissible n, and keep it fixed in time. At its n vertices run independent stationary diffusions

    dV_v(t)=sqrt(w^2-V_v(t)^2) dB_v(t)-V_v(t) dt.                   (4)

Their invariant law is uniform[-w,w]. For example V/w is one coordinate of Brownian motion on the unit two-sphere with generator (1/2)Delta, started uniformly; this gives existence, continuous paths, and the displayed coefficients. Equivalently the one-coordinate generator is (1/2) partial_v[(w^2-v^2)partial_v], whose boundary flux vanishes. The product process is reversible, also after mixing over the time-independent graph. Write H(t)=A+diag V(t).

Let phi_i be a real orthonormal eigenbasis and u_i=sqrt(n) phi_i. At simple spectrum, Hellmann--Feynman and second-order perturbation give

    partial_v lambda_i=phi_i(v)^2,
    partial_v^2 lambda_i=2 sum_{j!=i} phi_i(v)^2 phi_j(v)^2/(lambda_i-lambda_j).

These formulas can be used up to any stopping time on which the spectrum is simple. The spectrum is simple almost surely at each deterministic time by continuous independent diagonal potentials (also AW Appendix B). That fact alone is not a proof of pathwise noncollision for all times. The symmetric trace identities below avoid needing such a proof.

Fix E and rho=rho_{d,w}(E)>0. Put

    X_i(tau)=n rho [lambda_i(tau/n)-E],
    a_diff(v)=w^2-v^2,
    Q_ij^n=(1/n) sum_v a_diff(V_v) u_i(v)^2 u_j(v)^2.              (5)

For every simple-spectrum time the exact microscopic equations have

    d<X_i,X_j>/d tau = rho^2 Q_ij^n,                              (6)
    drift_i = -(rho/n) sum_v V_v u_i(v)^2
              +rho^2 sum_{j!=i} Q_ij^n/(X_i-X_j).                (7)

The factor 1/n in the time substitution is essential. For example the unscaled off-diagonal quadratic variation is sum_v a_diff phi_i^2 phi_j^2 = Q_ij^n/n; multiplication by (n rho)^2 and dt=d tau/n yields (6).

## 2. Exact smooth observables remove the local gap singularity

For f in C_c^infinity(R), let F_f(H)=sum_i f(X_i). The microscopic generator is the generator of (4) divided by n. At simple spectrum its action and carré du champ are

    L_n F_f = -(rho/n) sum_v V_v sum_i f'(X_i)u_i(v)^2
      +(rho^2/2) sum_i f''(X_i)Q_ii^n
      +rho^2 sum_{i<j} Q_ij^n [f'(X_i)-f'(X_j)]/(X_i-X_j),        (8)

    Gamma_n(F_f,F_g)=rho^2 sum_{i,j} f'(X_i)g'(X_j)Q_ij^n.        (9)

The divided difference in (8) extends continuously to f'' on the diagonal and is bounded by ||f''||_infinity. Thus a local inverse-gap moment is NOT inherently required for the smooth unlabeled process. These identities extend through coincident eigenvalues using the usual divided-difference formula for the Hessian of Tr f(H); the combinations of eigenspace coordinates are basis-independent. This is preferable to claiming an unproved labeled SDE valid for every time.

The finite-n reversibility identity is exact:

    E[F L_n G]=-(1/2)E[Gamma_n(F,G)].                              (10)

Indeed integrate each root potential by parts under the constant density on [-w,w]^n; a_diff vanishes at its endpoints. Smooth spectral trace functions and their smooth finite-dimensional compositions suffice. There is no graph boundary term. Formula (10) gives a possible form-convergence route around direct treatment of the drift in (8), but convergence of restricted static forms alone does not identify the projected time process: the hidden eigenvectors and fixed graph are also evolving-state information.

## 3. What the marked law predicts, and what it actually proves

In the source's microscopic marked limit at one root,

    (u_1,...,u_q) | tree environment  = sqrt(c) (g_1,...,g_q),
    c=Im m_o(E+i0)/(pi rho),

with independent standard normal g_i. Both c and V are part of the same root environment; they are not independent. For bounded continuous clipped versions of the integrand in (5), the empirical marked-law conclusion identifies its limit. The Gaussian fourth pairings predict, if the unbounded passage can be justified,

    kappa=E[(w^2-V^2)c^2],
    Q_ij^n -> kappa(1+2 delta_ij).                                (11)

The tree moment order needed for finiteness of kappa is a finite order, not every order simultaneously. The source can choose its initial weak-disorder threshold for the fixed orders used in its proof. No claim here transfers arbitrary moment orders to an unchanged threshold. Even granting kappa finite does not establish finite-graph quartic uniform integrability.

Under the anticipated coefficient passage, (9) has the candidate limit

    rho^2 kappa [2 sum_i f'(X_i)g'(X_i)
                    +(sum_i f'(X_i))(sum_j g'(X_j))].             (12)

This is the covariance of a beta=1 Dyson noise with clock rho^2 kappa plus an independent common Brownian translation of variance rate rho^2 kappa. The independent particle variance is 2 rho^2 kappa, so total diagonal variance is 3 rho^2 kappa. Dropping the common component gives the wrong answer already at the covariance level. This matches the fully proved fixed-block calculation in CALCULATIONS.md, although its bounded good-environment clock kappa_A and the all-site diffusion clock kappa are different weights and are not identified.

The local repulsion coefficient indicated by (7) is rho^2 kappa. That statement is an infinitesimal calculation, not a proved infinite Dyson equation. The far spectral sum in (7)/(8), together with the first term, must be compensated consistently at the fixed energy. For particles at macroscopic distance, a same-energy marked limit does not identify Q_ij. One must either close that passage or establish a sufficiently strong reversible-form/martingale argument that bypasses it. Static GOE stationarity by itself supplies neither.

Stationarity does help with time control once a genuinely L1 static estimate is available: for any integrable nonnegative state error R_n,

    E integral_0^T R_n(H(tau/n)) d tau = T E R_n(H(0)).             (13)

Thus a proved static L1 quartic-tail bound would immediately control its time-integrated version, with no union bound over a continuum of times. This removes an unnecessary extra obstacle. It still leaves count-weighted products, path tightness and identification of the limiting martingale or form, including any contribution from hidden coordinates.

## 4. A quantitative consequence of the supplied intercept argument

The source gives more than bare second-moment conservation if its actual Harnack argument is carried through quantitatively. This modest improvement is closed here as a feasibility estimate, and is insufficient for (11).

Fix s in R and y>0, with E+(s/n) inside the source's energy interval for all sufficiently large n. Let

    Z_{n,v}=Im G_vv(E+(s+iy)/n).

The source's small-intercept estimate has positive fixed exponents c,epsilon:

    P(B_v(E+(s+iY)/n)<Y^(-epsilon)) <= C Y^(-c)                  (14)

for Y sufficiently large, Y/n<=h, uniformly in the finite graph size. Its intercept B_v is independent of V_v. Harnack gives

    B_v(E+(s+iy)/n) >= (y/Y) B_v(E+(s+iY)/n),  Y>=y.             (15)

For T large choose Y=(yT/2)^(1/(1+epsilon)). On the complement of the event in (14), the right side of (15) is 2/T, so

    P(B_v(E+(s+iy)/n)<1/T) <= C_y T^(-delta),
    delta=c/(1+epsilon)>0.                                      (16)

There is no invalid interchange of n and a growing T: always Z_{n,v}<=n/y. For T<=n/y, the chosen Y is at most (n/2)^(1/(1+epsilon)), hence Y/n<=h for every sufficiently large n, uniformly over this entire nontrivial tail range. For T>n/y the Z tail vanishes. Bounded T are absorbed in constants. Apply conditional spectral averaging exactly as in the source:

    E[Z_{n,v} 1_{Z_{n,v}>T}] <= C_w P(B_v<1/T)
                             <= C_{w,y} T^(-delta).             (17)

Expectations include a uniform sampled vertex. Integration of this size-biased tail yields, for every 1<p<1+delta,

    sup_{n>=n0} E Z_{n,v}^p < infinity.                          (18)

Explicitly E Z^p=(p-1) integral_0^infinity t^(p-2) E[Z 1_{Z>t}]dt. Near zero use E Z<=C_w, and near infinity use (17).

With s=0,y=1 and the source coordinate x_i=n(lambda_i-E), the spectral decomposition reads

    Z_{n,v}=sum_i u_i(v)^2/(1+x_i^2).

Therefore any graph-and-potential measurable selected eigenvector with |x_i|<=S obeys u_i(v)^2 <=(1+S^2)Z_{n,v}. For fixed S and p as in (18),

    E[(1/n) sum_v |u_i(v)|^(2p) 1_{|x_i|<=S}] <= C_{S,p}.        (19)

The same bound applies to the maximum over eigenvectors in that fixed window, pointwise before averaging. This is an actual 2+epsilon' moment bound, not merely weak convergence. It can be combined with bounded clipping and stationarity (13). The source supplies only unspecified positive c and epsilon; it does not imply delta>1, which would be needed to obtain p=2 from (18). Neither (18) nor (19) closes the quartic overlap passage.

## 5. Testing the next possible upgrade

A bare second-moment counterexample would now be too weak, since (19) is available. For any fixed p<2, choose alpha with 1/4<alpha<1/(2p). Take a vector whose first coordinate is n^alpha and whose other coordinates are bounded quantile approximations to standard normal, then rescale to squared norm n. Its empirical law tends to N(0,1), its second moment tends to 1, and its empirical 2p moment remains bounded: the exceptional contribution n^(2p alpha-1) tends to zero. Nevertheless its fourth empirical moment grows at least as n^(4alpha-1).

This is ONLY a diagnostic for the proposed inference from (19). It is not an eigenvector construction, not a counterexample to the source or the desired dynamics, and does not respect all supplied resolvent or entropy identities. It explains why the explicit fractional-moment improvement is still short of a fourth-moment proof.

The clean primary HHW supplies a different mechanism: polynomially small entropy deficit plus a polylogarithmic maximum-amplitude bound, fourth-chaos coercivity, and a high-noise remainder. Its quantitative estimate is |E P(Y)-E P(G)| <= C B^(4/3) epsilon^(1/18), with epsilon<=c B^(-6). The Anderson source provides conditional full-environment Gaussian rigidity and exact second-moment retention. Its whitening and precision depend on that environment. No quantitative uniform fourth-chaos estimate for this conditional family, with finite-n tail/normalization errors controlled at the required scale, has been established here. Merely substituting the Gaussian mixture covariance into the clean deterministic whitening is invalid.

Thus the strongest construction currently closes (1)--(3), the finite-n identities (4)--(10), the useful stationarity reduction (13), and the fractional moment passage (14)--(19). It has not closed (11), nor the full time-process passage. No conditional version or bounded-environment restriction of the desired process is submitted as a nominee.
