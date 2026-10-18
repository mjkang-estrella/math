# r83: two heat-flow transport mechanisms and a moving-maximizer obstruction

Author derivation only; no frozen candidate or nomination. Prospective question: for every centered log-concave Lebesgue law on R^n with linear psi2 scale a, is it the pushforward of standard Gaussian measure by a Ca-Lipschitz map with universal C? The entire dimension-free class is retained. The source093 LSI and transport-entropy corollary do not themselves produce such a map. Family093 was already screened in I05 for entropy→full KLS; this is a different transport question, not a revival of that failed hypothesis upgrade.

## 1. Exact one-dimensional tilted example

For R>=2 set V_R(x)=v_R(|x|), where

- v(u)=u² for 0<=u<=R;
- v(u)=2Ru-R² for R<=u<=2R;
- v(u)=3R²+2R(u-2R)+(u-2R)² for u>=2R.

This C1 potential is convex. It satisfies V_R(x)>=2x²/3 everywhere (on the last piece, minimize 1-2R/u+3R²/u² at u=3R). Let mu_R have density Z_R^{-1}exp(-V_R). Symmetry centers it. Z_R>=int[-1,1] exp(-x²)dx>1.49, while

E exp(X²/16)<=sqrt(pi/(2/3-1/16))/1.49<2.

Thus a=4 works uniformly. The stipulated source gives a uniform LSI constant for every mu_R.

Tilt by h=2R. On [R,2R], hx-V_R(x)=R² exactly. On [0,R] it equals R²-(x-R)²; on [2R,infinity) it equals R²-(x-2R)². The negative half-line has integral at most int_0^infinity exp(-2Ru)du=1/(2R). Hence its normalizing integral divided by exp(R²) is between R and R+sqrt(pi)+exp(-R²)/(2R). The two subintervals [R,5R/4] and [7R/4,2R] each have probability at least a fixed positive constant for R>=2. Their distance is R/2. For independent tilted X,X', Var X=E(X-X')²/2>=cR².

Consequently the implication 'uniform original psi2/LSI gives uniformly bounded covariance of every linear tilt' is false. This does not refute the Gaussian transport question; it refutes one proposed sufficient interface.

## 2. Gaussian posterior refinement and integrated supremum failure

Consider the Gaussian posterior with density proportional to

exp(-V_R(x)-epsilon*x²/2+h*x),

where m=3R/2 and h=2R+epsilon*m. Within [R,2R] this is a constant times exp(-epsilon*(x-m)²/2). Outside that interval there is an additional nonnegative convex penalty: on the neighboring positive half-line it is the squared distance from the interval; globally it is nonnegative because 2Rx-R² is a supporting affine function of V_R. Therefore, after z=sqrt(epsilon)(x-m), the posterior equals a standard Gaussian on |z|<=sqrt(epsilon)R/2 and is bounded above by its unnormalized density elsewhere.

When sqrt(epsilon)R>=K, Gaussian tail integrals show uniformly that its centered variance satisfies

|epsilon*Var(X)-1|<=C(1+K³)exp(-K²/8).

The mean displacement is bounded by the corresponding first-tail integral; this supplies the centering correction. Choosing a sufficiently large fixed K makes epsilon Var(X)>=0.99. No moment estimate is inferred solely from mass convergence.

For the Ornstein-Uhlenbeck interpolation Y_t=rX+sqrt(q)Z, r=exp(-t),q=1-r², epsilon=r²/q, write f_t=dLaw(Y_t)/d gamma. Differentiating its Gaussian convolution gives exactly

(log f_t)''(y)=-epsilon+(r²/q²)Var(X | Y_t=y).

The posterior above corresponds to y=(q/r)h. For t>=1, epsilon<=1/(exp(2)-1)<0.157. If epsilon R²>=K², the displayed Hessian is at least -epsilon+0.99/q>=0.98. The interval 1<=t<=log R-log(2K) satisfies this condition for sufficiently large R. Thus

int_0^infinity sup_y [(log f_t)''(y)]_+ dt >= c log R.

This is a quantitative failure of the global-in-space Hessian integration route to a universal reverse-OU Lipschitz bound. It strengthens the mere unbounded-tilt-covariance observation: adding the Gaussian posterior curvature and integrating time does not repair the supremum estimate.

Kim–Milman's actual flow construction uses W_t=-grad log f_t, and expands the forward flow under a pointwise Hessian sign. The standard differential estimate for its inverse gives exp(int sup lambda_max(Hess log f_t)_+). The family above makes this certificate diverge while its original psi2 and source LSI constants remain bounded. We do not claim that the actual transport map's Lipschitz constant diverges.

## 3. Second mechanism: retain trajectories rather than a moving spatial maximum

The preceding bad observation centers are

y_t=(q/r)(2R+epsilon*m)=2R exp(t)+(m-2R)exp(-t).

Their derivative is 2R exp(t)-(m-2R)exp(-t). At such a point the posterior mean is approximately m, and the exact score identity is

partial_y log f_t(y)=-epsilon*y+(r/q)E[X|Y_t=y].

Up to the controlled Gaussian-tail error, W_t(y_t)=r(2R-m)=R exp(-t)/2. The maximizing centers move at speed of order R exp(t), whereas the flow at those centers moves at speed of order R exp(-t). They are not one flow trajectory. Replacing the trajectory integral by the spatial supremum loses precisely this information.

The remaining plausible route is a bound along every actual characteristic:

sup_x int_0^infinity lambda_max(Hess log f_t(S_t(x)))_+ dt <= C,

or a matrix/Jacobian estimate allowing directional cancellations, under the original psi2 hypothesis and the source's entropy inequality. Neither source093's global entropy dissipation nor its integrated average covariance statements directly gives a bound uniform over all starting points. Exceptional remote characteristics cannot be discarded for a globally Lipschitz map. The calculation above identifies a potentially useful moving-maximum mismatch but does not prove this trajectory estimate, even in high dimension. No narrower transport target or obstruction-only result is nominated.

## 4. Why the source's averaged information bound does not close route two

For an arbitrary unit direction, the original psi2 bound and the independent Gaussian noise give a universal subgaussian constant for Y_t, uniformly in t. Hence P(|Y_t|>=R exp(t))<=2 exp(-cR² exp(2t)). The bad centers y_t above lie beyond R exp(t) for t>=1. Their neighborhoods of radius at most one therefore have exponentially tiny output probability. An averaged posterior or Fisher-information estimate can remain uniformly bounded while the spatial Hessian supremum remains near one for log R time units.

The operative source07 Proposition `prop:information-upper` is even more specialized: it is a limsup bound for Gaussian covariance observations of the normalized near-extremal tensor/matrix fields along the source's contradiction sequence, with observation caps and time fixed before that limit. It is not a uniform bound for arbitrary posterior covariance at arbitrary original-space points. Source02 entropy dissipation and Gaussian-channel identities are averaged over conditioning labels. Applying them at an observation of exponentially small probability would require a new conditional estimate; the existing mean bound cannot simply be evaluated at that label.

A genuine route-two closure must exploit that one characteristic cannot follow all bad centers, or construct a different transport with a dimension-free Jacobian bound. The source LSI controls scalar entropy but currently supplies no such deterministic characteristic control. In dimensions greater than one, the derivative is a time-ordered matrix product; a bound for a scalar density ratio or determinant alone would not bound its largest singular value. These are unresolved estimates, not formal counterexamples to the prospective full target.

## 5. The obstruction example itself has a uniformly Lipschitz transport

This gives a useful check that Section2 did not accidentally refute the target. Let F_R be the distribution function of mu_R and Phi the Gaussian distribution function. The increasing transport T_R=F_R^{-1} composed with Phi has a Lipschitz constant bounded independently of R.

Indeed, V_R(x)<=x² everywhere as well: on [R,2R] subtract (x-R)² from x², and beyond 2R the difference is 2Rx-3R²>=0. Also V'_R(x)>=x for x>=0, checked on each of the three pieces. Normalization obeys 1.49<=Z_R<=sqrt(3*pi/2).

For x>=1, convexity gives the upper-tail hazard

h_R(x)=f_R(x)/(1-F_R(x)) >= V'_R(x) >= x.

On the other hand, integrating the lower density bound Z_R^{-1}exp(-u²) on [x,x+1] gives

1-F_R(x)>=c exp(-(x+1)²).

If z>=0 satisfies Phi(z)=F_R(x), the Gaussian upper bound 1-Phi(z)<=exp(-z²/2)/2 combined with that lower bound implies z<=C(x+1). The Gaussian hazard satisfies h_gamma(z)<=C(1+z); this follows, for instance, by integrating its density on [z,z+1/(1+z)]. Therefore

T'_R(z)=h_gamma(z)/h_R(x)<=C(1+x)/x<=2C.

For 0<=x<=1, f_R(x)>=exp(-1)/sqrt(3*pi/2), so directly T'_R(z)=phi(z)/f_R(x)<=C. Symmetry treats negative x. Absolute continuity extends the derivative bound to global Lipschitz continuity; the densities are positive continuous.

In one dimension every orientation-preserving flow map has the quantile coupling, so this is also a check on the limiting heat-flow transport, whenever that limit is constructed. The global-in-space Hessian integral is only a sufficient upper certificate and is grossly nonsharp for this family. The quantile argument is classical elementary transport and supplies no new full-dimensional result. In higher dimension, no corresponding single scalar quantile controls the operator norm of the matrix flow derivative. This remains the precise transition that the second mechanism has not paid.
