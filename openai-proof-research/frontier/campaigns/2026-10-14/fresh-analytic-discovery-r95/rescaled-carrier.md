# Rescaled carriers: exact physical derivative versus spectral filling

Live author derivation, not a full-flow theorem or independent verdict. The full desired operation is a smooth probability-preserving flow whose entire centered Koopman representation is simple Lebesgue on R. No spectral-component substitute is proposed.

Use first-stage physical coordinates (theta,u,a). Let V(u) be fixed, smooth, positive, with V' positive on the packet support. Let

 H_N'=N(V+Delta_N), |Delta_N|<=1/N,
 sigma_N(a)=1/N+J_1(a)/N²,
 (q,v,w)=(u,a,theta-H_N(u)).

For simplicity the display initially fixes J_1. Its dependence on N can be allowed below if ||J_1||_(C1)=o(N), with all stationary-phase errors chosen small by the usual successive parameter choices. The first canonical flow is

 X_N=sigma_N(a)[H_N'(u) partial_theta+partial_u].

Now perform a second passage in (q,v,w), with

 K_M'(v)=M(c+sigma_N(v)+Delta_M), |Delta_M|<=1/M,
 tau_M(w)=(1+d(w))/M, d=J_2/M,
 beta_N=1/(1+cN), c>=1.

The rescaled second flow in the first physical coordinates is exactly

 Y= A(a,w)[H_N'(u) partial_theta+partial_u]
       + beta_N(1+d(w))/M partial_a,
 A=beta_N(c+sigma_N(a)+Delta_M)(1+d(w)).

This follows by pushing forward partial_q and partial_v under the explicit chart inverse. It does not invoke a formal logarithm of a diffeomorphism.

## Baseline cancellation

With d=0 and Delta_M=0,

 A-sigma_N=(beta_N-1)J_1(a)/N².

Multiplication by H_N'=O(N) gives physical vector-field error O(||J_1||/N). Thus time rescaling really removes the earlier unrescaled integer-carrier obstruction at the level of the principal vector field. This is a potential mechanism, not a mistaken appeal to integer periodicity.

## The next jitter is differentiated through a rapidly winding spare angle

Let E_theta=(A-sigma_N)H_N'. Since partial_u w=-H_N',

 partial_u E_theta = - beta_N(c+sigma_N+Delta_M)(H_N')² d'(w)
                       +(A-sigma_N)H_N''.

On any fixed compact u interval with V bounded below by a positive constant, the first coefficient is bounded below by c_0 N, uniformly in c>=1 for large N and M. The second term has supremum at most

 C [ ||J_1||_(C1)/N + ||d||_infinity + N/M ].

The rounding contribution is harmless when M is chosen large compared with N and the first-stage data. Since theta ranges over a full circle independently of u,a, every value of w is available with u fixed. Consequently

 ||Y-X_N||_(C1) >= c_0 N ||d'||_infinity
                    - C [||J_1||_(C1)/N + ||d||_infinity + N/M].       (1)

Also C0 convergence forces ||d||_infinity->0 in this canonical rescaling, provided ||J_1||/N->0 and N/M->0: the theta coefficient is V(u)d(w) plus uniformly vanishing terms. Therefore C1 convergence in this regime forces

 N ||d'||_infinity ->0, and hence N osc(d)->0.                       (2)

The lower bound uses the actual physical chart, not norms in a changing coordinate system. A constant part of d only changes the clock and does not fill frequency gaps; (2) concerns its variation.

## Spectral consequence for a transported finite packet array

Assume the first transported angular indices j lie in N[s_0,s_1], 0<s_0<s_1<infinity, with discarded squared norm tending to0. This is exactly the finite compact-support stationary localization in the first source passage. For every fixed N, take M sufficiently large that the second stationary-phase localization has arbitrarily small discarded mass. Its second indices ell satisfy

 ell/M = j(c+sigma_N(v)) + arbitrarily small support enlargement.

The exact rescaled real temporal frequency is

 lambda=beta_N (ell/M)(1+d(w)).

For each j it lies in an interval of length at most

 C [ ||J_1||_infinity/N² + osc(d) ] + support-enlargement error.     (3)

Indeed beta_N j is bounded uniformly, osc(sigma_N)=osc(J_1)/N², and beta_N j(c+sigma_N)=O(1). The common part of d shifts the intervals but does not affect this bound. Choose support enlargements so their total contribution over O(N) indices tends to0; M may then be increased to control the discarded stationary mass. Pushforward contracts total variation, so no uniform derivative bounds on the varying jitter law are needed for this support conclusion.

There are O(N) first indices. Thus the output spectral mass is concentrated, up to a vanishing error, on a union E_N with

 |E_N| <= C [||J_1||_infinity/N + N osc(d)] + o(1) ->0             (4)

whenever the physical C1 convergence conditions above hold. If w_0 is any fixed nonnegative L1 density of mass1, then integral_(E_N) w_0->0 by absolute continuity of the Lebesgue integral. A normalized output density q_N concentrated on E_N therefore satisfies

 ||q_N-w_0||_1 ->2,
 ||sqrt(q_N)-sqrt(w_0)||_2² ->2.                                  (5)

For the second assertion, split the Hellinger overlap over E_N and its complement and use Cauchy–Schwarz; both pieces tend to0. These limits are maximal loss, not merely absence of a quantitative rate.

This calculation obstructs the particular two-pass architecture: flatten the nearly periodic first chart by a rescaled carrier, then restore a fixed absolutely continuous target by one smooth jitter in its winding spare angle. It does not disprove a different coherent-frame construction, multiple coupled passages, a different physical coordinate placement, or smooth simple-Lebesgue flows. In particular it is not a nominated supporting result.

## Reading boundary

The first passage stationary localization and exact output-frequency formula were read in the pinned source144 Section02 lines165–310; weighted neutral refresh lines410–499 was also read. Source phase folding is not silently reused for the real-line spectrum. The formula above is new author bookkeeping applied to those explicit coordinate maps. No primary regularity/scattering theorem is invoked in this calculation.
