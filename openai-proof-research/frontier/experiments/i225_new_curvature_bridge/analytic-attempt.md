# I225 analytic attempt — working mathematics

This file is an evolving calculation, not a nomination. Pinned OpenAI statements and their lower operations are accepted, not audited.

## Target selected after the initial screen

Fix a smooth closed connected Riemannian manifold `(M,g)`, dimension `n>=2`, with weak MTW for `c=d_g^2/2`. Fix `0<lambda<=Lambda`, and a source probability `rho=r vol_g` with `lambda<=r<=Lambda`. For target probabilities `mu_i=f_i vol_g`, `lambda<=f_i<=Lambda`, write `T_i` for their optimal homeomorphic representatives.

The ambitious target Q is a constant `C=C(M,g,lambda,Lambda)` such that, for every such source and every such target pair,

`integral d_g(T_0(x),T_1(x))^2 d rho(x) <= C W_1(mu_0,mu_1)`.

Thus the map norm, rather than its square, has exponent one half. This is stronger than the general manifold stability theorem and is not merely spatial Holder regularity. It is NOT proved here. Target boundedness and positivity matter: discrete-target examples are not counterexamples to Q.

Use the negative-cost convention `u_i(x)+c(x,y)+v_i(y)>=0`, with equality at `y=T_i(x)`. Define

`h_i(x,y)=u_i(x)+c(x,y)+v_i(y)`.

## Route A: global dual-gap coercivity

Exact cancellation gives

`integral [h_0(x,T_1(x))+h_1(x,T_0(x))] d rho`

`= integral (v_0-v_1) d(mu_1-mu_0) <= 2 diam(M) W_1(mu_0,mu_1)`.

Each `v_i` is `diam(M)`-Lipschitz. Therefore Q follows if the integrated coercivity estimate

`integral d(T_0,T_1)^2 d rho <= A integral [h_0(x,T_1)+h_1(x,T_0)] d rho`  (IC)

holds uniformly. Pointwise quadratic coercivity of a single gap would suffice but is substantially stronger than IC. The pinned lifted-section theorem only supplies power coercivity with an unspecified exponent; replacing its power by two is an unpaid step.

## Route B: intermediate-time regularization

For `0<t<1`, the accepted foundation gives `w_i,t=Q_t u_i` in `C^{1,1}`, with

`-C_g/(1-t) g <= Hess w_i,t <= C_g/t g`.

Its inverse pole/momentum maps are Lipschitz with constants depending only on `(M,g,t)`, uniformly for all potentials. This is an inverse projection of the intermediate graph, not a uniform Lipschitz estimate for the time-one transport maps.

One possible route would compare `grad Q_tu_0` and `grad Q_tu_1` by a variational energy estimate, reconstruct the two endpoint graphs by geodesic flow, and integrate in a common intermediate reference measure. The difficulty is that the two transported intermediate measures are different. No identity justifies substituting the source measure for either one. Also the displayed Hessian bounds deteriorate at both endpoints. Neither a time-one limit with fixed constants nor IC follows from the stated interface.

Further source reading and counterexample attempts follow below.

## A complete, limited consequence: the existing power survives perturbations

This section records what is actually paid. It is a standard strong-c-concavity/duality transfer, **not a proposed substantial finding**.

Fix the geometry and density bounds above. The pinned `Uniform-Bi-Holder-Transport-from-Weak-MTW.../build/sections/conclusion.tex`, using its lower proposition `jet:contradiction`, gives constants `C_0<infinity`, `beta>0`, `r_0>0`, common to the entire density class, with

`F(r) <= C_0 r^beta,  0<r<r_0`,

where `F` is precisely the supremum of the oscillation of `v` on `S_r(x;u,v)`, defined in `sections/scales.tex`. These are constants on a fixed manifold; their dependence is not explicit. Put

`q=min(beta,1)`, `r_*=min(1,r_0/2)`.

Let `D=diam_g(M)` and let `L_exp` be a finite common Lipschitz constant for `p -> exp_x p` on `|p|<=D`, for all `x`. Smoothness on this compact disk bundle supplies `L_exp`; no inverse exponential bound is used. Set

`B=max(8 L_exp^2(1+C_0), D^2 r_*^(-q))`.

For every admissible reference pair and every `x,y in M`,

`d(y,T(x))^2 <= B h(x,y)^q`.                                      (P1)

Proof: choose a minimizing logarithm to `y` and one to `T(x)`. Both lie in the lifted section of height `h(x,y)`. If `0<h<=r_*`, the pinned convex-section diameter inequality gives

`d(y,T(x))^2 <= 8 L_exp^2 [h+F(h)] <= 8 L_exp^2(1+C_0)h^q`.

At `h=0`, put both logs in every positive-height section and let that height decrease to zero. For `h>r_*`, use `d<=D`. This proves (P1) at all points, including cut pairs. No assertion about smoothness of the cost at these pairs enters the argument.

The cancellation displayed in Route A and Jensen's inequality now prove

`integral d(T_0,T_1)^2 d rho <= B [2D W_1(mu_0,mu_1)]^q`.             (P2)

Indeed the two gaps are nonnegative, so the integral of either one is bounded by their sum. Apply (P1) for `T_0` at `y=T_1(x)`, and apply concavity of `s^q`. Thus the map-norm exponent is `q/2`, not `q`. The source's spatial exponent can also be chosen `q/2`. There is no guarantee in the read source that `q` exceeds the exponent `1/6` for the **squared** map distance in Kitagawa–Letrouit–Merigot v2, Theorem 1.2. In particular this calculation does not establish an improvement over that primary theorem.

For completeness, (P1) handles both marginal and cost perturbations. Let `rho_hat,mu_hat` be arbitrary probability measures on `M`; neither is required to have a density. Let `c_hat` be continuous with `||c_hat-c||_infinity<=delta`, and let `gamma_hat` couple these measures with `c_hat`-cost at most its optimal value plus `epsilon>=0`. Define

`E=W_1(rho,rho_hat)+W_1(mu,mu_hat)`.

Then

`integral d(y,T(x))^2 d gamma_hat(x,y) <= B(2DE+2delta+epsilon)^q`.    (P3)

Proof: `u,v` are each `D`-Lipschitz. With `Opt_c` denoting minimum cost,

`integral h d gamma_hat <= Opt_c(rho_hat,mu_hat)-Opt_c(rho,mu)+DE+2delta+epsilon`.

Gluing optimal marginal `W_1` couplings to an optimal transport plan proves `|Opt_c(rho_hat,mu_hat)-Opt_c(rho,mu)|<=DE`, since `c` is separately `D`-Lipschitz. This gluing argument does not require absolutely continuous perturbed measures. Apply (P1) and Jensen. Notice that (P3) compares with `T(x)` at the perturbed source coordinate. It is not, without a further coupling argument, a distance between plans with different source marginals.

Gallouet–Merigot–Thibert v1, Theorem 5 and Proposition 8 already contain the abstract modulus transfer behind (P2) and the fixed-marginal part of (P3). Their Proposition 10 contains the marginal gluing mechanism. Extending the elementary estimate to a bounded cost error does not meet the requested contribution standard.

## Route A failure: power coercivity does not become quadratic

There is no valid passage from (P1) with `q<1` to a common quadratic gap. The following exact diagnostic explains why spatial bi-Holder behavior and semiconvexity alone are insufficient.

On `[-1,1]`, for `0<a<1`, set

`phi(x)=|x|^(1+a)/(1+a)`, `phi*(y)=a|y|^(1+1/a)/(1+a)`.

Their Fenchel gap equals the quadratic-cost gap for

`u(x)=phi(x)-x^2/2`, `v(y)=phi*(y)-y^2/2`,

and their contact map is `T(x)=sign(x)|x|^a`. This is a homeomorphism with an `a`-Holder forward map and a Lipschitz inverse; both potentials are semiconvex with lower bound `-1`. Nevertheless

`h(0,y)/|y-T(0)|^2 = [a/(1+a)] |y|^(1/a-1) -> 0`.

The example has uniform source density `1/2`, but the target density is

`f(y)=(2a)^(-1)|y|^(1/a-1)`.

It vanishes at zero. Products give the same diagnostic in dimensions at least two. **This is not a counterexample to Q**: it fails Q's positive target lower bound and closed-manifold hypotheses. It does refute using only semiconvexity, homeomorphism and bi-Holder regularity to infer quadratic coercivity. A proof of Q must use the positive-density input in an additional way.

The read primary criterion in Gallouet–Merigot–Thibert obtains a positive quadratic modulus by quantitative nondegeneracy of a smooth contact Hessian and smooth twisted cost on a compact admissible set. Their Theorem 28 requires a `C^1` map and `C^2` potential. Those are missing here, and the squared-distance cost is not globally smooth across cut pairs. Adding these assumptions would recover an existing theorem, not solve Q.

## Route B: a quantitative source-constant extraction and its obstruction

The foundation proof of `geo:intermediate` chooses `s=(1+t)/2`. The radial index comparison gives a supporting difference with Hessian at the contact point at least

`kappa_g(s-t) I = kappa_g(1-t)I/2`.

After reducing the common smooth-branch radius so that this Hessian loses at most half along the short geodesic, Taylor integration permits

`b_t = kappa_g(1-t)/8`.

The permitted radius `r_t` depends on uniform smooth action-branch bounds on the compact, radially shortened minimizing-vector sets at times `t,s`. The source supplies no rate for that radius as `t` approaches one. This is a choice extracted from the accepted proof, not a claim of optimality. It does not give a uniform positive `b_t` at time one.

At a fixed `t`, the inverse graph projection is uniformly Lipschitz, but a proposed comparison using a common uniformly positive intermediate density has a separate problem. In a Euclidean chart consider the positive symmetric derivative

`A_L=diag(L,L^(-1),1,...,1)`, `L>=1`.

Its determinant is one. Constant density one transported linearly by `A_L` gives constant density one at both endpoints (on the corresponding domains). At the midpoint, however,

`det((I+A_L)/2)=(2+L+L^(-1))/4`,

so the intermediate density is `4/(2+L+L^(-1))`, which tends to zero. Thus two-sided determinant bounds cannot produce a uniform positive midpoint-density bound. This is an exact **local matrix/domain model**, not a constructed counterexample on a fixed closed manifold with the full hypotheses of Q. It invalidates the determinant-only step of this route.

For the same reason, endpoint volume bounds cannot control condition numbers: `det A_L=1` while `||A_L||=||A_L^(-1)||=L`. Any proof importing uniform ellipticity from those volume bounds has an unpaid estimate. The pinching and value-space renormalization in family 357 do not apply to these transport Jacobians: no summable directional Bochner defect for the transport potentials has been supplied.

## Exact remaining problem and verdict

Q is neither proved nor disproved. A sufficient missing estimate is (IC), uniformly over the positive bounded density class. A pointwise quadratic gap would be stronger than necessary. To make the intermediate approach work instead requires a coercive comparison on the two different intermediate measures, with constants controlled by `(M,g,lambda,Lambda)` and a justified reconstruction of the common-source endpoint norm; no such estimate is proved here.

The fully proved statements are (P1)–(P3) and the two explicit diagnostic models. Their mechanisms are elementary transfers or obstructions, not a new substantial curvature/transport theorem. **Do not increment the accepted count.** Neither independent parent gate has been run by this research agent.
