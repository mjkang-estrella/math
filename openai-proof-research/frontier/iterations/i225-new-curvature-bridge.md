# I225 — curvature and noncollapse discovery

**Outcome: no substantial finding nominated; accepted count increment zero.** The strongest attempted target is a common square-root stability estimate for transport maps on a fixed weak-MTW manifold with both endpoint densities bounded above and away from zero. Two distinct routes leave a precise coercivity estimate unpaid. A weaker power estimate is fully proved, but it is a standard transfer and is not offered for either parent gate.

All pinned OpenAI theorems and lower proof operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` were accepted. This is fresh discovery, not an audit. No subordinate agents or live other-agent outputs were used. Only the assigned I225 outputs and fully read page excerpts were written; nothing was staged, committed or published.

## Target and exact quantifiers

Let `(M,g)` be a fixed smooth, compact, connected, boundaryless Riemannian manifold of dimension `n>=2`. Assume the pinned weak MTW inequality for `c=d_g^2/2` at every strictly pre-cut minimizing velocity and every perpendicular tangent pair. Fix `0<lambda<=Lambda` with a nonempty probability-density class.

For every source `rho=r vol_g` and targets `mu_i=f_i vol_g` satisfying `lambda<=r,f_i<=Lambda` almost everywhere and unit integrals, let `T_i` be the unique optimal homeomorphic representatives supplied by the pin. The unproved target is

`integral_M d_g(T_0(x),T_1(x))^2 d rho(x) <= C W_1(mu_0,mu_1)`,       (Q)

with `C` depending only on `(M,g,lambda,Lambda)`. Thus the `L^2` map norm would have exponent `1/2`. Neither smooth densities nor cut separation nor a bound on derivatives of densities is assumed. Q is **not proved or disproved** here.

## Screen and source overlap

The three screened families were 356, 357 and 360; no replacement family was used. The actual 356 characterization and its Hessian companion already supply the distributional-to-geodesic comparison interface. Standard Alexandrov consequences cannot be counted again. The actual 357 theorem gives dimension-only distortion but a point-dependent chart neighborhood. Its lower construction already converts summable directional Bochner defects into charts. Ordinary summable dyadic GH errors also give bi-Lipschitz charts by Gigli–Violo v1, Theorem 2.6; the published numbering differs. Neither repackaging qualifies.

The historical I07 report already left general cut separation under weak MTW unresolved. I225 did not recycle that as an achieved result. Instead it chose Q. Read scopes and exact rescaling dependencies are recorded in [reading-and-failures.md](../experiments/i225_new_curvature_bridge/reading-and-failures.md), and source provenance in [input-authentication.json](../experiments/i225_new_curvature_bridge/input-authentication.json).

## What is fully paid, and why it does not qualify

For the negative-cost dual potentials, write

`h(x,y)=u(x)+d_g(x,y)^2/2+v(y)>=0`.

The pinned Hölder manuscript proves, in its actual scalar gap formulation, `F(r)<=C_0 r^beta` below a common `r_0` on the fixed density class. Put `q=min(beta,1)`, `r_*=min(1,r_0/2)`, `D=diam(M)`, and choose a common forward exponential-map Lipschitz constant `L_exp` on `|p|<=D`. Then

`B=max{8L_exp^2(1+C_0),D^2 r_*^(-q)}`

gives the all-points estimate `d_g(y,T(x))^2<=B h(x,y)^q`. Convexity of the lifted gap section proves this without differentiating the cost at a cut pair. Dual cancellation and Jensen give

`integral d_g(T_0,T_1)^2 d rho <= B[2D W_1(mu_0,mu_1)]^q`.           (P)

The [analytic attempt](../experiments/i225_new_curvature_bridge/analytic-attempt.md) gives the full proof, including zero/large gaps, and an extension to arbitrary perturbed marginals, bounded cost error, and suboptimal plans. These are standard modulus/duality/gluing transfers. Gallouet–Merigot–Thibert v1, Theorem 5 and Propositions 8/10, already supply that abstract mechanism. The pin does not quantify `beta` or imply `q>1/6`; therefore (P) is not even asserted to improve the explicit general-manifold estimate of Kitagawa–Letrouit–Merigot v2, Theorem 1.2. Source constants are not uniform over changing metrics.

## Two attempted routes and the unpaid estimate

**Route A: global variational coercivity.** The exact identity

`integral [h_0(x,T_1(x))+h_1(x,T_0(x))] d rho`

`= integral(v_0-v_1)d(mu_1-mu_0) <= 2D W_1(mu_0,mu_1)`

shows that a sufficient missing estimate is

`integral d(T_0,T_1)^2 d rho <= A integral[h_0(x,T_1)+h_1(x,T_0)]d rho`, (IC)

with `A=A(M,g,lambda,Lambda)` for the entire class. The pin supplies the power version, not IC. A one-dimensional Fenchel power-map example explicitly refutes inferring pointwise quadratic gap growth from semiconvexity and bi-Holder homeomorphism alone. Its target density vanishes, so it is not a counterexample to Q. Positive target density would have to enter a new argument. Adding the smooth contact-Hessian nondegeneracy in GMT recovers their existing criterion rather than a new theorem.

**Route B: intermediate-time regularization.** The foundation gives `Q_tu` in `C^{1,1}`, inverse pole/momentum Lipschitz bounds, and local quadratic pole growth. Its proof permits `b_t=kappa_g(1-t)/8` after reducing a common smooth-branch radius; no rate for that radius as `t` tends to one is given. These are inverse intermediate-graph bounds, not endpoint-map Lipschitz bounds. Furthermore, `A_L=diag(L,L^(-1),1,...)` has endpoint Jacobian determinant one while midpoint determinant `(2+L+L^(-1))/4` diverges. Thus determinant-only endpoint-density information cannot justify a common positive intermediate density. This is a local matrix diagnostic, not a global counterexample. No coercive comparison of the two different intermediate measures, with justified endpoint reconstruction, was obtained.

## Verdict and provenance

The fully proved statements have existing mechanisms; Q and IC remain unpaid. Do not nominate P, basic topology, rectifiability, chart transfers, cut separation, or either diagnostic model as the tenth substantial finding. No worldwide novelty is claimed from search misses. The parent owns both independent gates, neither of which this research pass ran.

The [primary-source index](../sources/i225_new_curvature_bridge/literature.md) distinguishes actual readings from search leads. Existing pinned copies were reused, and every new retained source is an explicitly page-limited excerpt read in full. Detached SHA-256 hashes of the final outputs accompany the handoff.
