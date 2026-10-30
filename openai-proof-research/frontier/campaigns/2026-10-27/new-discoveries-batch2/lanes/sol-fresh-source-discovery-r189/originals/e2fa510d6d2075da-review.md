# Independent T373E135 correctness review r1

**Full PASS at the entire unchanged frozen scope, relative to the stipulated Source373 statements and operative proof operations.** All P1–P10 close. No mathematical repair or unresolved frozen obligation was found. This is the first independent correctness round of this role. There are no inherited independent T373E135 objections or responses. The expanded arguments below check the submitted proof, rather than replacing it with a restricted result. No contribution, novelty, acceptance, count, or downstream assessment is made.

Reviewer: Codex / GPT-6.1-Sol / high / default service tier. The independent trust roots are the detached hashes in the assignment. The frozen statement is exactly 2,630 bytes, SHA256 `cc80f307514d0fe7ab47079b6cda7d47abb7ce4c80aa616d0ebc02cc1b96e939`; the reviewed author proof has SHA256 `b3159d956644b4fd5befcf55de5a965eb91278798f6b8f57f713a84aab0d2172`. No original author file was repaired. The author’s assertion that nothing is deferred, and the parent’s intake, are not pass premises. Neither are the artifact controls or finite covariance examples.

## 1. Geometry, all fixed parameters, and integrability (P1)

I read Source373’s actual `local.tex`, `certificate.tex`, `proof.tex`, and entire `riesz.tex`, as well as its introduction, splitting argument, approximation section and bibliography. In the Riesz proof the fixed-coordinate minimization is in **(x,z), with y fixed**. It inherits the strictly positive (x,z)-Hessian on the convex product of the central and negative outer balls. The common-ball lemma sets `Y_k=X_k^{-1}` and `W_k=Z_k Y_k`. These are the interfaces used here; a contact-set assertion by itself would not suffice for quadratic detachment.

Fix any permitted d, alpha, construction and cube. No further shrinking of that cube is necessary in this review. Its closure and all four images are compactly inside their respective open source components. For fixed y=Y_k(t1), the stationary minimizer of `F_k=c_alpha-u_0-v_k` is `(t1,W_k(t1))`. Every segment from that minimizer to `(t0,W_k(t2))` remains in the source’s convex product balls. The union of these segments, as the three parameters vary in the compact cube, is a compact subset of that product. Continuity and source positivity therefore supply a **uniform** positive lower Hessian eigenvalue on this union. Taylor’s integral remainder gives

`r_k(t0,t1,t2) >= c0 (|t0-t1|²+|W_k(t2)-W_k(t1)|²)`.

Each W_k is bi-Lipschitz on the closed cube. Near the diagonal in the pair of parameter points this follows from its invertible derivative and a local inverse on a neighborhood of the compact image; away from that diagonal it follows from compactness and injectivity. Thus the preceding bound controls `|t1-t0|²+|t2-t0|²`. The reverse bound follows by Taylor expansion from `(t0,t0,t0)` along a segment in the **latent** convex cube, using the bounded Hessian of the smooth pullback r_k. This proves the author’s global two-sided estimate (1) on the full closed latent product, not only near the diagonal.

Since `r_k(t,t,t)=0` and its gradient vanishes there, (1) implies uniform positivity of `K_k=D²_(t1,t2)r_k(t,t,t)`. In coordinates `(x,h)=(t0,t1-t0,t2-t0)`, the identities `r_k(x,0)=0` and `D_h r_k(x,0)=0` make the tangent and mixed Hessian blocks vanish. The normal block is precisely K_k. Its determinant is bounded above and away from zero.

The source certificate excludes every component pattern except the two ordered branch patterns and their permutations, with exact equality graphs. This holds for the Riesz exponent alpha at hand by the actual all-dimension/all-exponent proof. On any forbidden compact product the extended slack R is lower semicontinuous, and collisions have value infinity. A zero minimum would be an actual contact in that forbidden pattern, contrary to the certificate. Thus the minimum is positive (or identically infinite); finitely many products give a positive common gap. This argument does not claim smoothness across collisions.

The specified bump and its square root extend smoothly by zero across every cube face and corner. Near a face at distance delta, derivatives of log f grow polynomially in delta^{-1}, whereas f decays as exp(-c/delta). All finite drift moments, `integral f|log f|`, and the initial Lyapunov moments are consequently finite. Compact change of variables under the branch diffeomorphisms gives the asserted smooth physical density and square root. The bounded log determinant proves all terms in C_* finite. Constants throughout may depend on every fixed datum; there is no parameter-uniform conclusion.

## 2. The full covariance prescription (P2)

Write the symmetric positive `2d x 2d` matrix A in d-dimensional blocks. The off-diagonal blocks need only satisfy `A21=A12^T`. The d-by-2d row matrix `R_A=(-A11/2,-A22/2)` uses the two symmetric diagonal blocks, not an assumption that A12 is zero or commutes with them. In `(z,h1,h2)` coordinates the proposed matrix is

`S = [[beta I_d, R_A], [R_A^T, A]]`.

Its Schur complement relative to A is `beta I_d-R_A A^{-1}R_A^T`. Taking beta larger than its supremum in operator norm plus one makes this complement uniformly positive. The smooth A field on a neighborhood of the cube extends globally by a cutoff supported inside that neighborhood and a fixed positive matrix outside it. Convexity of the positive cone, compactness of the transition region and a constant exterior give uniform ellipticity, boundedness and bounded derivatives. Choose beta after this extension; its supremum is finite.

The fixed invertible matrix L sends `(z,h1,h2)` to `(z,z+h1,z+h2)`. For `C=LSL^T`, the three diagonal blocks are respectively `beta I`, `beta I+R_1+R_1^T+A11`, and `beta I+R_2+R_2^T+A22`, all equal to beta I. With `D(z0,z1,z2)=(z1-z0,z2-z0)`, the identity `DL=(0,I_(2d))` gives `DCD^T=A` exactly. Off-diagonal blocks are unrestricted. This is a 3d-dimensional elliptic covariance, not a product of two d-dimensional covariances.

Uniformly positive matrices with bounded derivatives have a smooth positive square root with bounded derivatives of the orders needed here; for example the resolvent integral for the square root differentiates under the integral using the common spectral bounds. Thus sigma is globally Lipschitz and bounded. Evaluation of this field at z0 preserves these properties on R^(3d). Taking `A=K_k^{-1}` is legitimate on an open neighborhood of the full closed cube by the positivity already proved. No algebraic feasibility obligation remains.

## 3. Local solutions, nonexit, and exact marginal stationarity (P3)

The joint drift is smooth on Q³ and locally Lipschitz, while sigma is globally Lipschitz. Local strong solutions and pathwise uniqueness therefore hold up to exit from compact subsets of Q³. There is no assertion that the drift is bounded up to its boundary.

For `V(r)=2/(a²-r²)`, direct differentiation gives

`V'=4r/(a²-r²)²`, `V''=4/(a²-r²)²+16r²/(a²-r²)³`.

At either endpoint `(V')²` has order delta^{-4} and V'' has order delta^{-3}; hence `V''-(V')²` is bounded above on the interval. Let Phi be the sum of V over all 3d scalar coordinates. Its Hessian has no cross-coordinate terms, so the joint generator of Phi uses only the constant diagonal covariance blocks. It is bounded above by a fixed constant. Phi is positive, has finite expectation at the diagonal initial law, and diverges at every part of the boundary.

Stopping at the first level Phi>=n, including time zero when necessary, Itô and localization imply

`P(tau_n<=S) <= (E Phi(Z(0))+c S)/n`.

The martingale term is integrable at this localization. The bound forces the explosion/exit time to exceed every finite S almost surely. The solution extends uniquely and continuously in the open cube. In particular, a path on a finite time interval has a positive random distance from the boundary.

For particle i its martingale part N_i has `d<N_i^j,N_i^l>_s=beta delta_jl ds`. Lévy’s characterization in the **joint** filtration makes `N_i/sqrt(beta)` a d-dimensional Brownian motion, independent of the initial sigma-field. The different particles’ Brownian motions may be correlated. Each particle nevertheless satisfies the autonomous equation with diffusion sqrt(beta) I and drift `(beta/2)grad log f`. Local pathwise uniqueness and the same nonexit argument give uniqueness in law for that equation. Within one particle the scalar coordinates are autonomous and their driving Brownian coordinates are independent.

The author’s reflecting approximation justifies the invariant law without applying a theorem for a cube with a singular drift. Here are its boundary and limit details. On a scalar interval `I_n=[-a+1/n,a-1/n]` for sufficiently large n, the restricted coefficients are smooth bounded coefficients. Reflect at its two endpoints and use the normalized density `f_n=exp(-V)/integral_(I_n)exp(-V)`. For a Neumann test function h,

`integral_(I_n) L_1 h f_n = (beta/2)[h' f_n]_(boundary)=0`.

Equivalently the probability current `(beta/2)(f_n'+V'f_n)` vanishes identically. Invariance follows directly by applying this equality to the Neumann backward semigroup: differentiating its integral against f_n gives zero and its initial value is the integral of the original test function. These are regular scalar reflecting equations on each fixed inner interval, where existence and uniqueness follow from the interval Skorokhod reflection construction with Lipschitz drift. No regularity theorem on the original cube, or lower bound for the original flat density, is used.

Couple this stationary reflected equation and the unreflected scalar solution with the same initial f_n point and Brownian motion until the first endpoint hit. The level of V at these endpoints tends to infinity, whereas the expectations of V under f_n are uniformly bounded. The stopped Lyapunov inequality therefore makes their probability of disagreement before any fixed S tend to zero. The initial f_n converge to the scalar bump in total variation. Markov kernels contract that distance, so the unrestricted laws started from the limiting bump are the limits of these f_n laws. Since the reflected laws are f_n at every time, the limiting scalar bump is invariant. Taking products and using autonomous uniqueness proves **each** particle marginal is f at every time. Correlation of the joint noise causes no change to this conclusion.

Consequently every finite drift moment at each deterministic time is its fixed integral against f; in particular `E sum_i |b(Z_i(s))|²=3 beta² I(f)/4`. Fubini gives finite drift energy on every bounded time interval. This is an analytic stationarity statement, not a numerical inference.

## 4. Stopped Girsanov and its limit (P4)

Let the driftless global process have the same random diagonal initial point. Its initial law can be singular in R^(3d), because both path laws use exactly that same law. Put `v(z)=sigma(z0)^{-1} b_joint(z)` inside Q³. Stop when the path leaves an inner compact set and when accumulated `integral |v|²` reaches n. Before stopping v is bounded; after stopping set it to zero. Define this progressively measurable control on the entire path space, using its value only before that stopping time.

Under the driftless law the exponential `exp(integral v dB - (1/2)integral|v|²)` is a true martingale by boundedness on each fixed time horizon. Its conditional expectation given the initial point is one. Changing measure preserves the initial distribution and gives the stopped drifted equation, followed by the **global driftless equation** after stopping. Local uniqueness, then global driftless uniqueness, identifies this law with the corresponding glued strong solution.

For this stopped law P^n and the unchanged driftless path law Q,

`KL(P^n|Q)=(1/2) E_(P^n) integral_0^(S wedge tau_n) |v|² ds`.

Indeed under P^n the stochastic integral in log likelihood has the shifted Brownian martingale part plus its compensator; its mean is zero, since the stopped energy is bounded. The expectation is under P^n, not Q. Up to stopping, P^n agrees with the original confined law P, so this energy expectation equals the stopped expectation under P. Uniform ellipticity and exact marginal stationarity bound it by `c S`, independently of n.

Couple P^n and P with the same original Brownian motion and initial point until the stopping time, then continue P^n without drift. Under P, nonexit on compact time intervals and finite integrated energy imply `P(tau_n<=S)->0`. Thus the path laws converge even in total variation by this coupling. Joint lower semicontinuity of relative entropy against the fixed Q yields `KL(P|Q)<=c S`; it does not require convergence of the likelihood ratios or an unstopped Novikov assertion. The terminal-time map then gives `KL(P_s|Q_s)<=c s`. This proves the exact orientation and small-time rate needed by the author, including for the singular diagonal initialization.

## 5. Deterministic parametrix and thin-density normalization (P5)

The operator is the global autonomous **nondivergence** operator `L=(1/2) C(z0):D²` on R^(3d), with no drift or killing. It meets the boundedness, spatial Hölder and uniform ellipticity assumptions in Pascucci–Pesce’s deterministic Section 4. I read its assumptions, construction, convolution proof, remainder estimate and lower-bound chaining, rather than only its theorem statements. None is applied to the confined process’s singular drift.

In their notation Gamma solves `partial_t Gamma=L_x Gamma` and acts on initial functions by integrating in the pole xi. For this autonomous operator its action equals `phi -> E_x phi(X_t)`: applying Itô to the backward solution along X up to time t-delta and then sending delta to zero identifies the two Cauchy solutions. The Gaussian bounds and bounded-data uniqueness justify this limit. Thus

`p_s(start,end)=Gamma(s,start;0,end)`.

It is the end variable, the pole of the backward equation, that is frozen in `Z=G_(s C(end_0))(end-start)`. Switching to a forward density PDE would require the adjoint and would change this bookkeeping; the proof does not do that switching.

For clarity the actual estimate follows from `H Z=(L_x-L_end)Z`. Hölder continuity of C and the Gaussian second-derivative estimate give `|HZ|<=c s^{-1+theta/2} g_cs`, for any fixed 0<theta<1, where g_cs is a wider normalized Gaussian in dimension 3d. The k-fold time-space convolution has bound

`c^k Gamma(theta/2)^k s^{-1+k theta/2} g_cs / Gamma(k theta/2)`.

Gaussian spatial convolution and the beta integral prove this inductively. The series converges and is bounded by `c s^{-1+theta/2}g_cs` on 0<s<=1. Convolution once more with Z gives `|Gamma-Z|<=c s^(theta/2) g_cs`. The paper’s volume-potential construction gives the Cauchy kernel under the above hypotheses. Its mass-one property comes from the constant solution with zero killing. Positivity can also be read from the diffusion identification. The near-diagonal estimate `Gamma>=Z-|Gamma-Z|` gives a positive lower bound for short times; Chapman–Kolmogorov along a chain of balls gives the global Gaussian lower bound. This supplies exactly the author’s (6) and the fixed-time lower estimate, with their stated orientation.

Use `F_s(z)=(x=z0,w=(z1-z0,z2-z0)/sqrt(s))`. Its inverse Jacobian is `s^d`, since the transverse dimension is 2d. Hence the comparison density is exactly

`q_s(x,w)=s^d integral f(t) p_s((t,t,t),(x,x+sqrt(s)w1,x+sqrt(s)w2))dt`.

The Gaussian upper bound, boundedness of f, and completion of squares in t give `q_s<=C exp(-c|w|²)` for every x and 0<s<=1. Specifically, the squared displacement divided by s is comparable, after minimizing the common shift, to `|w|²+|t-t_*(x,w,s)|²/s`. Its t integral contributes `s^(d/2)`, canceling `s^d s^(-3d/2)`. There is no missing power of s.

For the leading term substitute `t=x+sqrt(s)v`. The covariance frozen at the final point is C(x), because the field depends only on the first particle. The remaining Gaussian integral is

`integral_(R^d) G_(C(x))(-v,w1-v,w2-v)dv = G_(A(x))(w)`.

This is ordinary Gaussian marginalization in the coordinates `(z0,Dz)` with determinant-one linear change of variables, using `DCD^T=A`. It is valid for arbitrary correlated C. Uniform continuity of the zero extension of f and Gaussian domination imply locally uniform convergence on Q x R^(2d) to `q_0=f(x)G_(A(x))(w)`. The integrated remainder is at most `C s^(theta/2)exp(-c|w|²)`. This limit integrates to one. Tightness follows as well from the compact diagonal initial support and bounded diffusion coefficient (normal second moments are uniformly bounded). Thus q_s converges weakly to that probability density. In particular the determinant and Gaussian normalization are correct.

## 6. Density, second moments and entropy transfer at the flat boundary (P6)

The preceding kernel is positive, so Q_s has a positive density after integration of the initial diagonal law. Finite `KL(P_s|Q_s)` implies P_s is absolutely continuous. After F_s, data processing preserves the bound `KL(p_s|q_s)<=c s`. Pinsker therefore gives total variation convergence of p_s-q_s to zero, and p_s converges weakly to q_0.

Let `Dz(s)=M_s+B_s` denote the difference martingale and integrated difference drift, starting from zero. Its quadratic variation is `integral_0^s A(Z_0(v))dv`. Exact stationarity of Z_0 gives

`E|M_s|²/s = integral f tr A`.

Cauchy–Schwarz in time and the stationary finite second drift moment give `E|B_s/sqrt(s)|²<=c s`. Its cross term with `M_s/sqrt(s)` tends to zero by Cauchy–Schwarz. Hence the w second moments converge to those of q_0. The x marginal of p_s is f exactly, so its second moment already agrees with q_0. These facts give convergence of the entire Euclidean second moment in (x,w); mixed x-w moments are not needed for the isotropic Gaussian reference below.

At each fixed s>0 one can integrate the Gaussian **lower** kernel bound over a fixed inner ball of parameters carrying positive f mass. With x in the bounded closed cube, this gives `q_s(x,w)>=c_s exp(-C|w|²)` for a positive c_s depending on s. In particular `-log q_s<=C_s+C|w|²` on the support of p_s, including x near a face of Q. The upper bound already proved gives `log q_s<=log C`. Thus `integral p_s|log q_s|` is finite. Together with finite KL, this legitimizes

`H(p_s)=KL(p_s|q_s)+integral p_s log q_s`.

There is no assumption that f has a boundary lower bound. The inner ball is used only in this fixed-time cross-entropy estimate, whose constant need not be uniform as s tends to zero.

For the entropy lower limit take a fixed nondegenerate **isotropic** Gaussian g on (x,w). Weak lower semicontinuity of `KL(p_s|g)` and convergence of the second moments give `liminf H(p_s)>=H(q_0)`. The Gaussian log density is a constant minus a multiple of `|x|²+|w|²`, so the subtraction is justified exactly by those moments.

For the upper limit choose increasing compact rectangles K_n inside Q x R^(2d), exhausting that open set and with q_0-null boundaries. On each K_n, q_0 is positive and continuous, so local uniform convergence gives uniform convergence of log q_s to log q_0. Weak convergence then gives convergence of the restricted integrals. On the complement use only the global upper bound log C:

`limsup_s integral p_s log q_s <= integral_(K_n) q_0 log q_0 + (log C)(1-q_0(K_n))`.

Now send n to infinity. The absolute integrability of `q_0 log q_0` follows from `integral f|log f|<infinity` and the common spectral bounds on A. The right side tends to H(q_0). This is the required **upper** limit orientation; no unjustified dominated convergence of log q_s at the boundary is being asserted. With KL=O(s), both entropy limits agree.

The 2d-dimensional Gaussian has entropy with the author’s positive sign convention

`H(G_A)=-d log(2pi)-d-(1/2)log det A`.

Consequently

`H(P_s)=d log(1/s)+H(f)-d log(2pi)-d+(1/2)integral f log det K_k+o(1)`.

The entropy transformation uses `det(F_s^{-1})=s^d`. The sign of both the log s term and the Gaussian determinant term is correct.

## 7. Cost, stopped expectations, and collisions (P7)

The latent r_k and its first two derivatives are bounded on a neighborhood of the closed cube product. Apply Itô up to inner compact stopping times. Its stochastic integral has a bounded integrand, so is uniformly square integrable on every bounded interval. Its drift integrand is bounded by a constant times the joint drift norm, whose time integral is integrable by stationarity. Nonexit and dominated convergence therefore remove stopping from the expectation identity.

The diffusion term converges as v tends to zero to its value on the diagonal, by continuity, boundedness and continuous sample paths. To check the unbounded drift term quantitatively, bounded sigma and stationary `E|b_joint|²` give

`E|Z(v)-(T,T,T)|² <= C(v+v²)`.

Since the gradient of r_k vanishes on the diagonal and is Lipschitz on the closed latent cube, `E|grad r_k(Z(v))|²=O(v)`. Its contraction with the joint drift has expectation O(sqrt(v)) by Cauchy–Schwarz. This tends to zero despite the singular inward drift.

In `(x,h)` coordinates the only nonzero diagonal Hessian block of r_k is K_k; the covariance of h is A. Trace contraction is invariant under the constant linear change of coordinates, so

`C:D²r_k = tr(A K_k)=2d` at the diagonal.

Thus the generator expectation tends to d. Integrating over v in [0,s] gives `integral r_k dP_s=d s+o(s)` with an ordinary time-average limit; no unbounded remainder is discarded.

The actual recovered physical triples always lie in `Qbar x Y_k(Qbar) x W_k(Qbar)`. These three compact components have strictly positive mutual separation. Hence their Riesz costs are bounded for **every alpha>0**, including alpha>=d. The auxiliary driftless law can leave these components, but is used only for its entropy comparison kernel. It is never substituted as a physical competitor. No alpha<d restriction enters.

## 8. Twelve cells, finite competitors and minimizers (P8)

Each branch coupling has all three latent marginals equal to nu. Product pushforward and averaging over two branches and six coordinate permutations therefore gives exactly nu/3 in the central component and each of the four outer pushforwards with coefficient 1/6 in every physical coordinate. The twelve ordered cells are disjoint, and each recovered cell has mass 1/12. The product marginal reference restricted to the corresponding cell has mass `(1/3)(1/6)(1/6)=1/108` and normalized pullback nu³. Relative entropy under the product diffeomorphism is invariant. Therefore

`KL(pi_s^rec|mu³)=log 9+(1/2)sum_k H(P_s^k)-3H(f)`.

The integral of log f in each latent coordinate is H(f) by its exact marginal. Its absolute integrability was proved above, so this identity does not conceal an infinity-minus-infinity calculation. Inserting the two branch entropy formulas gives

`KL(pi_s^rec|mu³)=d log(1/s)+C_*-d+o(1)`.

The average of the two `(1/2)integral f log det K_k` terms is the required **quarter sum**. Combining with the cost `E+d s+o(s)` and setting s=epsilon proves the exact upper coefficient C_*. The `-d` from Gaussian entropy cancels the `+d` from the cost. The discrete correction is log 9, not log 12 or log 108.

For every positive epsilon, a fixed time 0<s<=1 already supplies finite cost and finite KL; no smallness of epsilon is needed for existence. On the compact support product the cost is nonnegative and lower semicontinuous and KL relative to the fixed probability mu³ is lower semicontinuous. The set of exact-marginal couplings is weakly compact. A minimizing sequence therefore has a minimizing limit with finite objective. Any two minimizers have finite densities relative to mu³, and strict convexity of `r log r` makes their midpoint strictly improve the objective if they differ. The cost is affine on these finite-cost plans. Hence the minimizer is unique. Permutation invariance of constraints and objective makes this minimizer symmetric. No density positivity for the optimizer is required.

## 9. Symmetric selection, Laplace measure and exact lower coefficient (P9)

The source contact coupling has value `E=3 integral u dmu`, and every unregularized optimizer has zero nonnegative slack. Thus every such optimizer is supported on the twelve graphs. A symmetric optimizer is determined by finite central-parameter measures eta_k of total combined mass one followed by uniform permutation. Its marginal on the Y_k component is `(1/3)Y_k#eta_k`. Comparing with the prescribed `(1/6)Y_k#nu`, and using injectivity, forces `eta_k=nu/2`. This proves exactly the claimed uniqueness **within the permutation-invariant class**. It does not assert uniqueness of all unregularized optimizers.

The recovery upper bound tends to E, KL is nonnegative, and cost is lower semicontinuous. Every weak cluster point of the entropic minimizers is consequently an unregularized optimizer. Symmetry passes to the weak limit, so every cluster point is the stated pi_0. Compactness proves weak convergence of the whole family.

Consider the finite references `tau_e=epsilon^{-d}exp(-R/epsilon)mu³`. On forbidden products their masses are at most `epsilon^{-d}exp(-delta/epsilon)` times the reference mass, using the positive forbidden gaps, including at collisions with exp(-infinity)=0. There is no unproved kernel approximation there.

On an allowed ordered k-cell the pullback reference density is `f(t0)f(t1)f(t2)/108`. Substitute `tj=t0+sqrt(epsilon)wj`. The Jacobian epsilon^d cancels the prefactor. The global detachment bounds the integrand, including the domain indicators and any bounded test function, by

`C f(t0) exp(-c|w|²)`.

This is integrable on `Q x R^(2d)`, since the other two f factors are bounded. For interior t0 and fixed w the indicators eventually equal one, and Taylor gives the exponent `(1/2)w^T K_k(t0)w`. Zero extension of f handles all other points; cube boundaries have zero nu mass. Dominated convergence gives weak convergence, and convergence of total masses, to the graph measure with parameter density

`(2pi)^d f(t)^3/(108 sqrt(det K_k(t)))`.

This calculation includes all twelve cells, no unlisted boundary mass, and no reference-Jacobian from the physical diffeomorphisms: those have already been canceled by pullback of the specified product marginal measures.

For a probability P and finite positive M of nonzero mass, normalize M to a probability to obtain

`KL(P|M)=sup_(phi continuous) [integral phi dP-log integral exp(phi)dM]`.

This is the probability-reference Gibbs formula minus log M(total). It uses the author’s integral definition of KL; the alternative unnormalized-measure formula with a linear exponential integral is not being confused with it. Compactness allows continuous bounded tests; approximation of truncated log densities gives equality, including the infinite case. Each test expression is continuous under weak convergence of P and finite M with positive limiting mass. Taking the supremum gives the joint lower semicontinuity needed here.

For every exact-marginal plan with finite objective, direct substitution and boundedness of u give

`KL(pi|tau_e)=(integral c_alpha dpi+epsilon KL(pi|mu³)-E)/epsilon-d log(1/epsilon)`.

The sign follows from `log(d tau_e/d mu³)=d log(1/epsilon)-R/epsilon`. Apply joint lower semicontinuity to `pi_e -> pi_0` and `tau_e -> tau`. On each graph pi_0 has density f/12, so

`d pi_0/d tau = 9 sqrt(det K_k)/((2pi)^d f²)`

where f>0. Both measures give the boundary zero mass. Its log is integrable against pi_0 by the earlier entropy and determinant bounds. Integrating over the twelve graphs yields **exactly C_***. Thus the liminf lower coefficient equals the recovery upper coefficient. This proves the full value expansion without a density lower bound or a Gaussian claim for pi_e.

## 10. Separate cost and entropy expansions, and scope (P10)

Let `h_e=KL(pi_e|mu³)`, which is finite. Optimality gives the supporting-secant inequality `E_eta<=E_e+(eta-e)h_e` for every eta>0. For fixed lambda>1, use eta=lambda e and eta=e/lambda and the proved value expansion. The resulting lower and upper bounds for h_e are

`d log(1/e)+C_*-d lambda log(lambda)/(lambda-1)+o(1)`

and

`d log(1/e)+C_*-d log(lambda)/(lambda-1)+o(1)`.

The errors are o(1) for each **fixed** lambda: the value remainders at lambda e and e/lambda divided by a fixed multiple of e have that property. First take e to zero, then lambda down to one. Both constant corrections tend to `C_*-d`, giving the asserted entropy expansion. Subtract e h_e from the value to obtain the cost expansion `E+d e+o(e)`. There is no differentiation of an uncontrolled o(e) remainder and no exchange requiring a lambda-uniform estimate.

This closes existence and uniqueness for every epsilon>0, finite C_*, all three asymptotic formulas, and the stated weak convergence/unique symmetric limit for every fixed d>=2, alpha>0, stipulated source construction and admissible cube. It does not prove parameter-uniform remainders, an all-density result, a positive-everywhere marginal theorem, arbitrary particle number, a deterministic-regularity law, higher-order terms, or fluctuations of the actual optimizer. The Gaussian transverse density belongs to the constructed recovery and driftless comparison only.

## 11. Primary comparisons and decision limits

I read the actual operative Nenna–Pegon block/rate/lower passages, Pal assumptions and reverse-kernel proof, Cardoso-Perelló–González-Sanz–Nutz assumptions and complete EOT upper/completion proof, and Langevin/Girsanov and deterministic-parametrix passages specified in `reading-and-limits.md`. The broader Nutz–Zhong work was only partially read, with that limit retained. The author’s strongest comparison is compatible with this correctness proof: none of those alternative recovery methods is assumed impossible or used as an unpaid premise. The present exact three-marginal recovery is verified directly. In particular the stronger quadratic completion result does not require its separate lower-density hypothesis for EOT; the reviewed proof does not assert otherwise.

Source construction, geometry, exact contacts and approximation operations remain stipulated true, not truth-audited. The antecedents are credited without assigning a contribution verdict. No failure of a naive factorized construction is used to establish this theorem. Mathematical verification here consists of the arguments above, not the finite diagnostics, hashes, parent intake, chronological author claims, or a search-absence claim.

Required mathematical repairs: **none**. Unresolved obligations within the frozen theorem: **none found**. Evidence/search/isolation limitations remain as recorded separately and are not certificates of exhaustive history or priority. The initial filename-only discovery command was overbroad and truncated; that procedural limitation is expressly disclosed in the reading record rather than replaced by an assertion of perfect exclusion. Subsequent bounded scans and all operative semantic reads used the recorded exclusions. No independent other T373E135 review output was consumed.
