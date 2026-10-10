# I35 — splitting-invariant Gibbs bias: aggregation, source slices, and a precise stopping point

**Disposition.** UB and Q remain **unproved and not refuted**. The I34 entropic interfaces used below pass the independent mathematical audit, without a mathematical repair. Two constructions are developed: a mass-weighted cluster comparison with an exact entropy identity, and a source-slice rearrangement that isolates transverse redistribution. A reversible Gibbs kernel supplies an additional diagnostic. These give technical deductions, including uniform bias for collinear targets and a genuine growing regular-polygon Gibbs family. They do not establish the general estimate. The transport route is parked pending the single transverse-redistribution lemma in §6. No substantial finding is nominated.

All pinned OpenAI proofs and their internal operations are premises, not objects of an upstream audit. Original briefs, objections and reports are frozen. No agents, shared edits, staging, commits or publication were used. The parent controls integration and any subsequent independent proof/significance reviews.

## 1. Quantifiers, conventions and inherited interfaces

Fix a compact convex body $K\subset\mathbb R^d$, $d\ge2$, compact nonempty $Y$, and probability densities $c\le f\le C$ a.e. on $K$, with $0<c\le C$. Put $\rho=f1_Kdx$, $K\subset B_R$, $Y\subset B_L$, with $R,L\ge1$, and $P_K=\sum_j|\operatorname{proj}_{e_j^\perp}K|$. Throughout, finite targets have arbitrary positive masses and arbitrary distinct sites; zero masses are removed and identical physical sites are merged. Auxiliary cluster centroids may belong to $\operatorname{conv}Y\subset B_L$, which is permitted in every estimate used here.

For $\mu=\sum_i m_i\delta_{y_i}$, the entropic objective is

$$\int\tfrac12|x-y|^2d\gamma+\varepsilon\operatorname{KL}(\gamma\mid\rho\otimes\mu),\qquad \gamma\in\Pi(\rho,\mu).$$

Subtracting fixed second moments gives the equivalent objective $J_\varepsilon(\gamma)=-\int x\cdot y\,d\gamma+\varepsilon\operatorname{KL}(\gamma\mid\rho\otimes\mu)$. Write

$$p_i(x)=\frac{m_i e^{(x\cdot y_i-\psi_i)/\varepsilon}}{\sum_km_ke^{(x\cdot y_k-\psi_k)/\varepsilon}},\quad \int p_i\,d\rho=m_i,\quad T_\varepsilon=\sum_i p_i y_i=\nabla u_\varepsilon.$$

The true optimal map is $T_0=\nabla u_0$. Define

$$B=\int|T_\varepsilon-T_0|^2d\rho,\quad V=\int\sum_i p_i|y_i-T_\varepsilon|^2d\rho,\quad E=\int\sum_i p_i|y_i-T_0|^2d\rho=B+V.$$

UB asks for $B\le A(K,Y,c,C)\varepsilon$, simultaneously for every finite target and every source in this class, $0<\varepsilon\le1$. Q asks for $\|T_\mu-T_\nu\|_2\le A W_2(\mu,\nu)^{1/3}$ for arbitrary targets. Failure of UB alone would not refute Q.

### 1.1 Independent audit of the I34 entropic statements actually used

**PASS — normalization and stability.** Expanding the finite exponential sum gives $q_i=\psi_i-\varepsilon\log m_i$ in counting coordinates. The entropy chain rule gives $\operatorname{KL}(\gamma\mid\rho\otimes\mu)=\operatorname{KL}(\gamma\mid\rho\otimes\sum_i\delta_{y_i})+H(m)$; the last term is fixed. Therefore changing convention changes neither optimizer nor barycenter. DNWP's Theorem 3.1, including its conditional-KL proof, bounds the map difference by $(1+2\sqrt{H_\mathrm{forward}H_\mathrm{backward}}/\varepsilon)W_2$. Bounded supports give covariance operator bounds $L^2,R^2$, hence exactly

$$\|T_\varepsilon^\mu-T_\varepsilon^\nu\|_2\le(1+2RL/\varepsilon)W_2(\mu,\nu).\tag{1}$$

No factor two is lost by switching from full to half squared cost: the correlation formulation above uses the same $\varepsilon$ as DNWP. Reading Delalande's published §2.1, Theorem 2.1, Remark 2.1 and Corollary 2.2 confirms that its $o(\varepsilon)$ dual result is in counting coordinates, with fixed-configuration constants. Altschuler–Niles-Weed–Stromme §2.2 explicitly makes the same change of reference. I34's correction to the use of DNWP v1 equation (22) is valid. The unshifted relative dual cannot be substituted into that estimate.

**PASS — variance, and its limitation.** Direct differentiation gives $\varepsilon D^2u_\varepsilon=\operatorname{Cov}(Y\mid X)$. Every coordinate derivative of the globally smooth convex $u_\varepsilon$ lies in $[-L,L]$. Integrate its monotone derivative along each interval slice of $K$, then use $f\le C$:

$$V=\varepsilon\int f\Delta u_\varepsilon\le V_*\varepsilon,\qquad V_*=2CLP_K.\tag{2}$$

This argument applies directly to measurable $f$ and finite targets; no trace of $f$ on a facet is used. Orthogonal conditional expectation gives $E=B+V$, so (2) alone cannot bound $B$.

The I34 split-center test is correctly scoped. For $0<b\le a/2<1/4$, set $S=\nabla\max(-x,a,x)$ and $T=\nabla\max(-x,a-b/2+b|y|,x)$ on the uniform square. The feasible plan that splits the central strip of $S$ equally between $\pm be_2$ has the law of $T$ as target, barycenter $S$, variance $ab^2$, and bias $b/4+ab^2$. The middle half-width is $h(y)=a+b(|y|-1/2)$; integrating $|h-a|$ gives $b/4$, and the vertical second moment is $ab^2$. This plan is not Gibbs. Neither its convex barycenter nor its correct marginals repairs that missing property.

**PASS — genuine two-atom estimate.** For sites a distance $s$ apart along $n$, the projected source density is at most $C A_n$, where $A_n=|\operatorname{proj}_{n^\perp}K|$. The hard and logistic plus assignments have the same mass. Their left-to-right and right-to-left leakages are equal. Whichever logistic threshold lies farther toward one side, the leakage on the opposite side is bounded by $CA_n\varepsilon\log2/s$. Jensen then gives $B\le2CA_ns\varepsilon\log2$, including vanishing-mass limits by merging. This is a nonasymptotic marginal argument, not a dual-asymptotic estimate.

On the uniform square with masses $(m,1-m)$ at $(-e_1,e_1)$, integrating the logistic marginal gives

$$b_\varepsilon=2m-1+\frac\varepsilon2\log\frac{1-e^{-4m/\varepsilon}}{1-e^{-4(1-m)/\varepsilon}},\qquad T_\varepsilon=\tanh((x-b_\varepsilon)/\varepsilon)e_1.$$

At fixed $0<m<1$, the correction is $o(\varepsilon)$, $B/\varepsilon\to2\log2-1$, and $V/\varepsilon\to1$. The order is first $\varepsilon\downarrow0$ at fixed $m$. The divergent logarithmic-mass upper expression in DNWP does not identify the true bias coefficient.

**PASS — fixed-configuration coarea bound; GAP retained for its uniform onset.** For fixed smooth positive $f$ and fixed finite positive target, counting-dual error $\delta_\varepsilon=o(\varepsilon)$ gives the pairwise bound $p_j\le e^{2\delta_\varepsilon/\varepsilon}/(1+e^{d_{ij}/\varepsilon})$ on hard cell $i$. Coarea and dominated convergence give twice $\varepsilon\log2$ times the weighted facet jump budget. Positive cells exclude coincident triple tie planes; sections tend to their actual facets, including zero limits at lower-dimensional faces. The budget is at most $2CLP_K$. Thus I34's $\limsup B/\varepsilon\le4\log2\,CLP_K$ is correct with its fixed-configuration quantifiers. No uniform onset, measurable-source trace, or growing-target interchange follows.

**PASS — individual counting-dual obstruction and limiting order.** Equal-mass labels in a cluster obey $|c_i^\varepsilon-c_j^\varepsilon|\le R|y_i-y_j|$ by the ratio of their Gibbs probabilities. For I34's half-mass external site and $M$ central labels, the aggregate intercept is $\varepsilon\log\sum_i e^{c_i^\varepsilon/\varepsilon}$. First letting cluster diameter tend to zero at fixed $M,\varepsilon$ forces this aggregate intercept to zero, hence each central intercept tends to $-\varepsilon\log M$. Hard intercepts tend to zero. The stated oscillation divergence follows, but the physical map converges to the two-atom map. Section 2 below strengthens the entropic part of that convergence with a uniform geometric estimate.

**PASS — conditional implication UB ⇒ Q.** For finite targets, the triangle inequality, (1), and $\varepsilon=w^{2/3}$ give the cube-root norm bound when $w\le1$; bounded slopes cover $w>1$. At fixed target and $\varepsilon$, normalized finite dual minimizers converge under $L^1$ source approximation: marginal-ratio bounds make their coordinates precompact, and strict convexity modulo constants identifies the limit. Hard potentials converge uniformly along subsequences and their gradients converge a.e. and in $L^2$ by supporting inequalities and bounded slopes. This passes a genuinely uniform UB to measurable sources. Combining estimates before the target limit then permits finite nets and qualitative uniqueness/compactness to pass Q to arbitrary targets. None of these operations applies to the weaker fixed-configuration limsup.

This audit covers the entropic premises, not a new independent review of every I34 geometric calculation. The I33 obstruction and finite-atom proof were read in full; they are not substitutes for any uniform estimate below. All nine BT text interfaces were read under the stipulated-premise rule.

## 2. Construction A: physical clusters before dual comparison

### 2.1 Exact splitting invariance

Replace one physical atom of mass $m$ by coincident labels of masses $m\alpha_k$, $\sum_k\alpha_k=1$. For any feasible labelled coupling, let $P(x)$ be its total conditional probability at that location and $r_k(x)$ its conditional label proportions. Its entropy contribution is

$$\int P\log(P/m)\,d\rho+\int P\operatorname{KL}(r(x)\mid\alpha)\,d\rho.$$

The cost only sees the physical location. Replacing $r(x)$ by $\alpha$ preserves every label marginal and lowers entropy. Strict convexity therefore forces $p_k=\alpha_kP$ at the optimum. Thus the physical coupling, $T_\varepsilon$, $T_0$, $B,V,E$, and every projected physical conditional law in §3 are exactly unchanged. The counting intercept changes by $\varepsilon\log\alpha_k$; that label-dependent number is deliberately not the measured quantity.

This proves invariance for unequal as well as equal artificial splits. It uses the constrained optimizer, rather than assuming that arbitrary label probabilities split proportionally.

### 2.2 A cluster comparison without entropy loss

Partition the finite target labels into sets $A$. Define

$$M_A=\sum_{i\in A}m_i,\quad z_A=M_A^{-1}\sum_{i\in A}m_iy_i,\quad \bar\mu=\sum_A M_A\delta_{z_A},$$
$$r_1=\sum_i m_i|y_i-z_{A(i)}|,\qquad r_2^2=\sum_i m_i|y_i-z_{A(i)}|^2.$$

Repeated centroids may be treated as labelled sites and then merged using §2.1. Let $P$ be the fine entropic optimizer and $\bar Q$ the optimizer for $\bar\mu$. Lift $\bar Q$ to the fine labels by

$$Q(dx,i)=\bar Q(dx,A)\frac{m_i}{M_A}\quad(i\in A).\tag{3}$$

It has source marginal $\rho$ and individual target marginal $m_i$. Moreover $\operatorname{KL}(Q\mid\rho\otimes\mu)=\operatorname{KL}(\bar Q\mid\rho\otimes\bar\mu)$, and the centroid choice gives $\int x\cdot(y_i-z_A)dQ=0$. Hence $J_\varepsilon^{\mathrm{fine}}(Q)=J_\varepsilon^{\mathrm{coarse}}(\bar Q)$ exactly.

Collapse $P$ to $\bar P$. Entropy disintegration gives

$$\operatorname{KL}(P\mid\rho\otimes\mu)=\operatorname{KL}(\bar P\mid\rho\otimes\bar\mu)+I_A,$$

where $I_A=\int\sum_A P_A(x)\operatorname{KL}(P(\cdot\mid x,A)\mid(m_i/M_A)_{i\in A})d\rho\ge0$. The Gibbs form of $\bar Q$ implies the exact feasible-objective identity

$$J^{\mathrm{coarse}}_\varepsilon(\bar P)-J^{\mathrm{coarse}}_\varepsilon(\bar Q)=\varepsilon\operatorname{KL}(\bar P\mid\bar Q).$$

Indeed the logarithm of its density is $(x\cdot z_A-u(x)-\bar\psi_A)/\varepsilon$, and the two marginal potential terms cancel. Fine optimality and the same chain rule now prove

$$\boxed{\varepsilon\operatorname{KL}(P\mid Q)\le\int x\cdot(y_i-z_A)dP\le Rr_1.}\tag{4}$$

In fact applying the analogous feasible-objective identity to the fine optimizer gives the stronger exact equality

$$\varepsilon\{\operatorname{KL}(P\mid Q)+\operatorname{KL}(Q\mid P)\}=\int x\cdot(y_i-z_A)dP.\tag{5}$$

All densities are positive for this fixed finite problem; compactness makes the displayed quantities finite. There is no uniform lower mass assumption. Equations (4)–(5) also show that the correlation on the right is nonnegative, which is not imposed in advance.

For completeness, entropy controls the barycenter as follows. Pointwise, total variation between two conditional target laws is at most $\sqrt{\operatorname{KL}/2}$. Means of laws in $B_L$ differ by at most $2L$ times total variation. Integrating and using (4), while coupling each $y_i$ to $z_A$, gives

$$\boxed{\|T_\varepsilon^\mu-T_\varepsilon^{\bar\mu}\|_2\le r_2+L\sqrt{2Rr_1/\varepsilon}.}\tag{6}$$

Independently (1) gives the sometimes better bound $(1+2RL/\varepsilon)r_2$. Both estimates vanish for small cluster spread at fixed $\varepsilon$, uniformly in counts and masses. If cluster radii are $\delta_A$, then $r_1\le\sum_A M_A\delta_A$ and $r_2^2\le\sum_A M_A\delta_A^2$. No error is multiplied by the number of clusters or by an entropy of the label vector. This is a technical chain-rule/variational deduction, closely related to the KL comparison already used in DNWP's stability proof.

### 2.3 Aggregate Gibbs fields and genuine cycle cancellation

In counting intercepts $c_i=-q_i$, put

$$H_A(x)=\varepsilon\log\sum_{i\in A}e^{(x\cdot y_i+c_i)/\varepsilon},\qquad P_A(x)=\frac{e^{H_A(x)/\varepsilon}}{\sum_Be^{H_B(x)/\varepsilon}}.$$

These are exact aggregate probabilities; $\int P_A d\rho=M_A$. If $|y_i-z_A|\le\delta_A$, then

$$|\nabla H_A-z_A|\le\delta_A,\qquad \operatorname{osc}_K(H_A-x\cdot z_A)\le\operatorname{diam}(K)\delta_A.\tag{7}$$

The gradient is a within-cluster Gibbs mean. Artificial coincident splitting leaves $H_A$ unchanged because the split exponentials add to the old exponential. The non-affine residual in (7) is controlled geometrically, even when individual intercepts have arbitrarily large logarithmic corrections.

One must still recalibrate coarse marginals: replacing $H_A$ by an affine approximation does not automatically preserve $M_A$. Construction (3) and identity (5) supply an honest comparison to the recalibrated problem. They do not bound the correction between the coarse positive-temperature and coarse zero-temperature problems.

Here is the exact many-cell constraint that a cycle argument must use. Let $P_i^0$ be hard cells and $F_{ij}=\int_{P_i^0}p_jd\rho$. Both row and column sums equal $m_i$, so its off-diagonal part is a circulation and decomposes into directed cycles. For a cycle $i_1,\ldots,i_k,i_{k+1}=i_1$ and arbitrary $x_\ell\in P_{i_\ell}^0$, define the nonnegative hard gaps

$$d_{ij}(x)=x\cdot(y_i-y_j)+c_i^0-c_j^0.$$

With $\Delta_i=c_i^\varepsilon-c_i^0$, direct cancellation gives

$$\prod_{\ell=1}^k\frac{p_{i_{\ell+1}}(x_\ell)}{p_{i_\ell}(x_\ell)}
=\exp\!\left(-\varepsilon^{-1}\sum_{\ell=1}^k d_{i_\ell i_{\ell+1}}(x_\ell)\right).\tag{8}$$

This removes all dual corrections from the cycle. It does **not** permit replacing the integrals $F_{ij}$ by pointwise ratios at common points. Integrating a product over $k$ cell variables yields a $k$-fold object; a cycle decomposition of the integrated flow does not supply those conditional product laws. Also, cycle balance preserves vector increments, not sums of squared increments. I34's realized zigzag warns against bounding a long weighted path by target diameter. Thus (8) is a real Gibbs identity, but it has not paid the summed squared-jump budget $E=\sum_{ij}F_{ij}|y_i-y_j|^2$.

### 2.4 Quantitative multiscale cluster test

A known, target-uniform quarter-power estimate for this source class is enough to test extremely fine clusters without assuming Q. Write it as $\|T_0^\mu-T_0^{\bar\mu}\|_2\le H r_2^{1/4}$ for $r_2\le1$, with $H$ depending only on the fixed geometry and $C$. One explicit choice follows from the read Wang–Wang proof: its compensated error is at most $CL^3\operatorname{Per}(K)t^2/6$; its target repair gap is at most $2Rw$. Consequently

$$H=1+\sqrt{8R+(4/3)CL^3\operatorname{Per}(K)}\tag{9}$$

works by choosing $t=\sqrt w$. This is an existing quarter-power operation, not a new modulus. Combining it with (1) gives

$$|\sqrt{B(\mu)}-\sqrt{B(\bar\mu)}|\le(1+2RL/\varepsilon)r_2+Hr_2^{1/4}.\tag{10}$$

Thus any arbitrarily large, multiscale cluster refinement of a family already satisfying UB still satisfies UB along a sequence with $r_2=o(\varepsilon^2)$; the difference in square roots is $o(\sqrt\varepsilon)$. This permits arbitrarily unequal within-cluster masses. Nested clusters need not be compared level by level: collapse directly to their final centroids and use the total mass-weighted spread. Intermediate entropy losses do not accumulate. It excludes that precise proposed amplifier, while leaving clusters at larger geometric scales fully unresolved.

## 3. Construction B: conditional quantiles on physical source slices

This construction applies to every finite target and every measurable $c\le f\le C$ in any fixed dimension. It does not presume that a componentwise rearrangement is a multivariate optimal map.

Fix coordinate $j$. Write $x=z+te_j$, $z\in e_j^\perp$, and $I_z=\{t:z+te_j\in K\}$. Set $h_j(z)=\int_{I_z}f(z+te_j)dt$. Fibers with $h_j=0$ are omitted. Let $\rho_z^j(dt)=f(z+te_j)dt/h_j(z)$, an atomless probability on its interval. Under the actual Gibbs plan define the scalar conditional target law

$$\alpha_{j,z}^\varepsilon=\sum_i\left(\int_{I_z}p_i(z+te_j)d\rho_z^j(t)\right)\delta_{y_{i,j}}.$$

Define the hard scalar conditional target law

$$\alpha_{j,z}^0=(T_{0,j}(z+\cdot e_j))_\#\rho_z^j.$$

Both average to the same $j$th target-coordinate law when integrated against $h_j(z)dz$, but need not agree fiberwise. Repeated projected site values are merged. Let $G_{j,z}$ be the CDF of $\rho_z^j$ and $Q_{j,z}^\varepsilon$ the quantile of $\alpha_{j,z}^\varepsilon$. Put

$$R_j(z+te_j)=Q_{j,z}^\varepsilon(G_{j,z}(t)).\tag{11}$$

All objects have Borel versions: fiber integrals are measurable, and CDF/quantile comparisons at rational values give measurable selections. Endpoints, zero-length fibers and null tie sets are irrelevant. No division by a uniform positive fiber mass is used in an estimate.

The scalar function $t\mapsto T_{\varepsilon,j}(z+te_j)$ is nondecreasing, since $\partial_{jj}u_\varepsilon\ge0$. Hence its coupling with the nondecreasing $R_j$ is an optimal one-dimensional quadratic coupling. The actual conditional Gibbs law couples $T_{\varepsilon,j}(X)$ to $Y_j$ on that fiber. It follows that

$$\int|T_{\varepsilon,j}-R_j|^2d\rho_z^j
\le\int\sum_i p_i|y_{i,j}-T_{\varepsilon,j}|^2d\rho_z^j.\tag{12}$$

To see the scalar optimality without imposing strict monotonicity, any crossing pairs $a<a'$, $b>b'$ cost $2(a'-a)(b-b')$ more than their ordered swap. Quantile coupling removes all crossings; approximation by finite ordered partitions passes this statement to atomless source laws and arbitrary bounded scalar target laws. Flat intervals are allowed.

Similarly, $t\mapsto T_{0,j}(z+te_j)$ is nondecreasing a.e., as the derivative of a convex function on the line. Therefore

$$\int|R_j-T_{0,j}|^2d\rho_z^j=W_2^2(\alpha_{j,z}^\varepsilon,\alpha_{j,z}^0).\tag{13}$$

Define the **transverse redistribution** quantity

$$\mathcal F_\varepsilon=\sum_{j=1}^d\int h_j(z)W_2^2(\alpha_{j,z}^\varepsilon,\alpha_{j,z}^0)dz.\tag{14}$$

Integrating (12), summing coordinates and applying the Hilbert-space triangle inequality yields the exact useful reduction

$$\boxed{|\sqrt B-\sqrt{\mathcal F_\varepsilon}|\le\sqrt V\le\sqrt{V_*\varepsilon}.}\tag{15}$$

In particular, $B\le2\mathcal F_\varepsilon+2V_*\varepsilon$ and $\mathcal F_\varepsilon\le2B+2V_*\varepsilon$. The vector $R=(R_j)_j$ need not be a convex gradient or have law $\mu$. We use it solely as a common-source intermediate vector field in (15). Claiming either of those extra properties would invalidate the construction.

Every object in (11)–(15) is invariant under the exact splitting in §2.1. Even their coarse-graining continuity has a weighted, label-free bound. Let $\bar\mu,r_1,r_2$ be as in §2 and let $r_2\le1$. The product metric on the fiber laws, (4), data processing and Pinsker give

$$|\sqrt{\mathcal F_\varepsilon(\mu)}-\sqrt{\mathcal F_\varepsilon(\bar\mu)}|
\le r_2+2L\sqrt d\left(\frac{Rr_1}{2\varepsilon}\right)^{1/4}+Hr_2^{1/4}.\tag{16}$$

Here is the justification of the possibly less familiar middle term. First collapse the fine conditional law to its centroid; coupling each label to its centroid costs, after integrating all fibers and summing coordinate squared costs, at most $r_2^2$. Compare these collapsed laws with the coarse optimizer. Their joint law of $(z,Y_j)$ is a measurable image of $\bar P$, respectively $\bar Q$, so the integrated conditional KL is at most $\operatorname{KL}(P\mid Q)$. On each scalar target fiber, $W_2^2\le4L^2d_{TV}$. Cauchy–Schwarz and Pinsker bound its integrated cost by $4L^2\sqrt{\operatorname{KL}(P\mid Q)/2}$. Sum $d$ coordinates and take the square root. Finally couple the two hard projected laws by the same source point; their summed cost is at most the squared map distance bounded by (9). The product-space triangle inequality proves (16). Constants worsen as $\varepsilon\downarrow0$, as displayed; no limit exchange is hidden.

### 3.1 A completed all-atom subcase, and exactly what it avoids

If $Y$ lies on one affine line $y_*+\mathbb Rn$, both maps depend only on $r=n\cdot x$ apart from the common perpendicular component. The Gibbs scalar map and hard scalar map are nondecreasing, and both scalar target laws are the same global law. Applying the argument of (12) directly to this projected source gives

$$B\le V\le2CL A_n\varepsilon.\tag{17}$$

More precisely $2L$ can be replaced by the scalar target diameter. This holds for any finite count, arbitrary masses/separations, and bounded measurable source density; the lower density bound is unnecessary. No smooth approximation is needed. Product sources and product targets in rectangular domains similarly tensorize: the product of the one-dimensional optimizers has both marginals and the additive Gibbs exponential, so uniqueness identifies the optimizer; the hard map is the product of scalar monotone maps. This gives uniform bias for arbitrarily large product grids and multiscale product clusters.

These are technical scalar/tensor deductions, not nominations. General sources and targets do not supply equality of the conditional laws $\alpha_{j,z}^\varepsilon,\alpha_{j,z}^0$. The globally correct marginal only supplies their averaged equality.

### 3.2 A concrete check of the unpaid transverse term

For I34's non-Gibbs split-center feasible plan, repeat (11)–(14) using its conditional target probabilities. Its barycenter is $S$ and its true target map is $T$. On horizontal fibers, the projected feasible law has middle mass $a$, while the hard law has middle mass $h(y)$; the scalar transport cost is $|h(y)-a|$. Thus $\mathcal F_1=b/4$. On vertical fibers the monotone rearrangement of the feasible law is $b\operatorname{sign}(y)$ on $|x|<a$, and zero elsewhere. Comparing with the true middle region gives $\mathcal F_2=b^2\rho(\{|x|<a\}\triangle\{|x|<h(y)\})=b^3/4$. Therefore

$$\mathcal F=b/4+b^3/4,\qquad V=ab^2.$$

The ratio diverges at $b=a/2\downarrow0$. This independently verifies that global balance and convexity of the barycenter cannot prove the new lemma either. It is an obstruction to omitting Gibbs optimality, not an admissible UB counterexample.

## 4. A physical reversible Gibbs kernel, and why it is not a heat kernel

The backward conditional source laws are $\eta_i(dx)=p_i(x)\rho(dx)/m_i$. Draw $Y\sim\mu$ and, conditionally on it, two independent draws $X,X'\sim\eta_Y$. This constructs the symmetric coupling

$$\mathcal R_\varepsilon(dx,dx')=\rho(dx)\rho(dx')\sum_i\frac{p_i(x)p_i(x')}{m_i}.\tag{18}$$

Both marginals equal $\rho$: integrate $p_i(x')$ to $m_i$ and sum $p_i(x)=1$. Splitting an atom into proportions $\alpha_k$ changes its kernel contribution into $\sum_k\alpha_k p_i(x)p_i(x')/m_i$, exactly the old contribution. Thus this kernel is also splitting invariant.

Its Dirichlet energy for the entropic map is small:

$$\int|T_\varepsilon(x)-T_\varepsilon(x')|^2d\mathcal R_\varepsilon
=2\sum_i m_i\operatorname{Var}_{\eta_i}(T_\varepsilon)
\le2\sum_i\int p_i(x)|T_\varepsilon(x)-y_i|^2d\rho=2V.\tag{19}$$

The inequality is minimization over the conditional mean, using $y_i$ as a competitor. This is a genuine Gibbs construction with exactly verified marginals. It does not identify its low-energy field with $T_0$.

An isotropic source-displacement estimate for (18) is actually false: for a singleton target, $p_1=1$, the plan is the entropic optimizer for every $\varepsilon$, and $\mathcal R_\varepsilon=\rho\otimes\rho$. Its displacement is $2\operatorname{Var}_\rho X$, independent of $\varepsilon$. Diffuseness within a constant-map cell is harmless for (19), but rules out a generic heat representation with source step $O(\sqrt\varepsilon)$. Convex-gradient BV translation bounds cannot be applied as though such a step had been proved.

## 5. Adversarial true-Gibbs families

### 5.1 Growing regular polygons: a uniform pointwise comparison

Here is an explicitly solvable non-collinear family, including arbitrary growing atom count and oscillatory smooth source density. In $d=2$, take the unit disk $K$ and the $N\ge3$ unit regular-polygon sites $v_k=(\cos(2\pi k/N),\sin(2\pi k/N))$, each of mass $1/N$. Let $f$ be any bounded positive density invariant under rotation by $2\pi/N$; radial densities suffice. The hard potential is $u_0=\max_k x\cdot v_k$, since rotation gives equal sector masses. The Gibbs probabilities

$$p_k(x)=\frac{e^{x\cdot v_k/\varepsilon}}{\sum_\ell e^{x\cdot v_\ell/\varepsilon}}\tag{20}$$

also have mass $1/N$ by rotation. Their exponential form and marginal constraints prove that they are the actual entropic optimizer, with no numerical dual solution or asymptotic approximation.

In fact, for every $x$ off the hard sector boundaries,

$$|T_\varepsilon(x)-T_0(x)|^2\le1-|T_\varepsilon(x)|^2
=\operatorname{Var}(Y\mid X=x).\tag{21}$$

**Proof.** Rotate so $T_0=v_0=(1,0)$ and reflect so the polar angle of $x$ is $\theta\in[0,h]$, $h=\pi/N$. Ordering the sites by decreasing score gives $0,1,-1,2,-2,\ldots$, with the evident truncation and arbitrary resolution of equal scores. The average of the first $k$ sites is

$$a_k=\frac{\sin(kh)}{k\sin h}\,(1,0)\quad(k\text{ odd}),\qquad
a_k=\frac{\sin(kh)}{k\sin h}\,(\cos h,\sin h)\quad(k\text{ even}).$$

These formulas include the zero mean at $k=N$. For odd $k$ the coefficient lies in $[0,1]$. For even $k\ge2$ it lies in $[0,\cos h]$: $\sin t/t$ decreases on $(0,\pi)$, because $(\sin t-t\cos t)'=t\sin t>0$. Every $a_k$ therefore lies in the closed disk $D_0=\{z:|z|^2\le v_0\cdot z\}$, the disk with diameter $[0,v_0]$.

Any decreasing probability vector $p_1\ge\cdots\ge p_N\ge0$ is a convex combination of uniform prefix laws, with weights $\lambda_k=k(p_k-p_{k+1})$, $p_{N+1}=0$. These are nonnegative and sum to one, and the coefficient of the $\ell$th site is $\sum_{k\ge\ell}\lambda_k/k=p_\ell$. Consequently $T_\varepsilon=\sum_k\lambda_k a_k\in D_0$. Expanding $|T_\varepsilon-v_0|^2\le1-|T_\varepsilon|^2$ is exactly its defining inequality. This proves (21). ∎

Integration and (2) give $B\le V\le8C\varepsilon$ on the disk, uniformly in $N$ and $\varepsilon$. This controls true bias, not a divergent facet upper expression. It remains a symmetry-restricted geometric deduction, not a proposed general UB theorem or a substantial nomination.

For an explicit smooth oscillatory sequence use

$$f_k(x)=\pi^{-1}\{1+\tfrac12\cos(2\pi k|x|^2)\},\qquad k\in\mathbb N.$$

The substitution $s=r^2$ proves normalization. The common bounds are $1/(2\pi),3/(2\pi)$, while derivative norms grow. Thus $B/\varepsilon\le12/\pi$ for all $N,k,\varepsilon$. This includes $N\to\infty$, $k\to\infty$, and any simultaneous regularization scale, such as $\varepsilon=N^{-2}$. A genuine lower bound also follows without quadrature: $T_\varepsilon(0)=0$, $\operatorname{Lip}T_\varepsilon\le1/\varepsilon$, so on $|x|\le\varepsilon/4$ its distance from the unit hard target is at least $3/4$. For $0<\varepsilon\le1$,

$$9\varepsilon^2/512\le B\le12\varepsilon/\pi.$$

The lower bound is deliberately not claimed sharp. These families cannot amplify $B/\varepsilon$. Tensoring the source with uniform cube coordinates and giving sites zero extra coordinates gives the same conclusions in every fixed higher dimension.

### 5.2 An exact true-bias certificate with a nonproduct oscillatory source

On the square use the four sites $(\pm1,\pm1)$, equal masses, and

$$f_k(x,y)=\tfrac14(1+\tfrac12\cos(k\pi x)\cos(k\pi y)),\qquad k\ge1.$$

These are smooth with common bounds $1/8,3/8$, uniform coordinate marginals and independent sign symmetries, but are not product densities. The hard map is $(\operatorname{sign}x,\operatorname{sign}y)$. The exact Gibbs map is $(\tanh(x/\varepsilon),\tanh(y/\varepsilon))$: its product-form conditional probabilities have each target marginal $1/4$ by the sign symmetries. Thus, writing $t=e^{-2/\varepsilon}$,

$$\frac B\varepsilon=2\left[2\log2-1-2\log(1+t)+\frac{2t}{1+t}\right].\tag{22}$$

The identity follows by integrating $(1-\tanh z)^2=2-2\tanh z-\operatorname{sech}^2z$. Since

$$0\le\log(1+t)-t/(1+t)=\int_0^t\frac{s}{(1+s)^2}ds\le t^2/2,$$

we obtain the rigorous enclosure

$$2(2\log2-1)-2e^{-4/\varepsilon}\le B/\varepsilon\le2(2\log2-1).\tag{23}$$

The diagnostics certify rational enclosures using the convergent positive series for $\log2$ and $e>2$, rather than uncertified quadrature. This verifies the cost convention and the true optimizer at arbitrarily small displayed scales. It neither extrapolates a fixed-configuration onset nor tests only an arbitrary feasible plan.

### 5.3 What these attacks do and do not eliminate

The scalar/product proof handles growing grids, unequal masses and multiscale collinear clusters. The polygon proof handles genuinely non-collinear many-cell Gibbs flows with coalescing adjacent sites, equal masses tending to zero, and derivative-unbounded smooth source densities on one fixed body. The entropy comparison handles arbitrary atom splitting and sufficiently fine multiscale refinements of any controlled base family. None allows replacing a general weighted target by an equally weighted symmetric one. Macroscopic nonsymmetric cluster interactions and transverse conditional mass transfer remain unpaid.

No admissible sequence with $B/\varepsilon\to\infty$ has been constructed. No pair of optimal maps with a divergent cube-root ratio has been constructed either. The original non-Gibbs and divergent-dual tests retain exactly their narrower meanings.

## 6. One unpaid lemma and the decision to park this route

**Transverse Gibbs redistribution lemma (unproved).** With the fixed $K,Y,c,C$ and definitions (11)–(14), there is $A_\perp(K,Y,c,C)<\infty$ such that, for every finite physical target, every measurable $c\le f\le C$ probability density, and $0<\varepsilon\le1$,

$$\sum_{j=1}^d\int h_j(z)W_2^2(\alpha_{j,z}^\varepsilon,\alpha_{j,z}^0)dz\le A_\perp\varepsilon.\tag{TR}$$

This is a precisely defined scalar-transport quantity built from the actual Gibbs and hard marginals on physical source slices. It is unchanged by artificial splitting; (16) controls its finite-temperature cluster approximation without label entropy. It concerns how mass is redistributed *between* source fibers, after the within-fiber smoothing error has already been bounded in (12). It does not ask for an individual dual norm or an isotropic heat displacement.

Equation (15) proves that TR is equivalent to UB up to explicit additive variance constants: TR implies UB with constant $2A_\perp+2V_*$; UB with constant $A$ implies TR with constant $2A+2V_*$. This equivalence is a reduction, not a weakened premise asserted as a theorem. The new work has isolated a structural term; it has not made the central difficulty disappear by renaming it.

A proof would have to combine Gibbs optimality with the globally balanced but fiberwise different scalar target laws. Equations (7)–(8) remove artificial label corrections but do not estimate this redistribution. The reversible kernel (18) controls a different Dirichlet energy. The generic split-center computation proves that their missing Gibbs structure cannot be dropped. The symmetric/scalar examples prove TR in restricted classes through bias or direct ordering, not for arbitrary configurations. We therefore park this transport route pending a proof or an admissible Gibbs counterexample to TR; another fixed-count calculation, individual-dual bound or fixed-configuration limsup is not a reason to reopen it.

## 7. Source comparison, preservation and reproduction

The complete preprint tree has 749 manuscript directories; the lagging catalogue contains 719 linked manuscript entries. The full 9,340-file reused corpus is checked against its SHA256/Git manifest and the complete tree, without copying the corpus. All nine BT text files are selected with pinned raw URLs and Git blobs. The catalogue, tree and corpus manifest are read-only dependencies, not fresh claims of semantic reading of every proof.

Current retrieved metadata confirms DNWP v1, Altschuler v1, Delalande arXiv v2 (the separately retained published PMLR text is the interface used), LM v3, Ruan v1, Wang–Wang v1, BK v2 and Ford v1; the HAL response identifies v1. The exact requests, response bytes, extraction dependencies and failures are retained or referenced by hash. The first exploratory web response was not serialized; the second exact search request/response is retained. Neither noisy search hits nor absence of hits proves novelty. No new claim of reading the blocked published DNWP PDF is made; its historical failure bytes and the earlier nonpaper BK response remain preserved by dependency hashes.

The operation-level comparisons use the actual read interfaces:

- [DNWP v1](https://arxiv.org/abs/2404.02855v1), equations (7)–(12), Theorem 3.1 and full conditional-KL proof, Proposition 4.1/appendix and Theorem 4.3: the exact conventions, covariance identity and target stability. Cluster comparison (4)–(6) is a technical entropy-chain-rule application of related variational operations. Its estimate is not a general bias estimate.
- [Delalande's published paper](https://proceedings.mlr.press/v151/delalande22a/delalande22a.pdf), §2.1, Theorem 2.1, Remark 2.1, Corollary 2.2, and [Altschuler–Niles-Weed–Stromme v1](https://arxiv.org/abs/2106.11862v1), Theorem 1.3 and §2.2: fixed-data counting-dual asymptotics. They do not justify a uniform onset for I34's coarea limit.
- [Wang–Wang v1](https://arxiv.org/abs/2610.09640v1), Lemmas 6–8 and proof of Theorem 1: compensated error, density comparison and target repair yield exactly the known quarter-power input (9). [Mérigot HAL v1](https://hal.science/hal-05616391v1), Theorem 3.4 and §4, estimates arbitrary feasible-plan error by the square root of its correlation gap; its semi-discrete consequence uses a fixed-data cost-gap asymptotic. These operations do not supply TR.
- [LM v3](https://arxiv.org/abs/2411.04908v3), Theorem 2.1 and complete four-step proof: comparable-density variance coercivity via tilted log-concave reference measures; Proposition 2.2: interpolation. [Ruan v1](https://arxiv.org/abs/2610.07577v1), Theorem 8 and its proof: quarter-power at bounded source density, with its density parameter retained. Neither is a linear-potential estimate or the fiberwise Gibbs redistribution bound.

The collinear/product result is standard scalar rearrangement and tensorization. The polygon statement uses elementary prefix averages of ordered roots of unity. No exact full-scope duplicate search or independent significance acceptance is claimed for its packaging; symmetry removes the general mass-calibration difficulty, so it is not promoted as a substantial result. The source-slice construction and the kernel are technical representations with a proved reduction and a proved limitation.

From the project root run:

```bash
python frontier/experiments/i35_splitting_invariant_entropic_bias/diagnostics.py
python frontier/experiments/i35_splitting_invariant_entropic_bias/verify.py
```

The diagnostics check exact entropy-chain factorizations as formal logarithmic identities, coincident unequal splitting and reversible-kernel invariance, scalar quantile costs and the split-center transverse formula, prefix decompositions, and rational true-bias enclosures for (22)–(23). Discrete algebra checks are labelled as such, not passed off as continuous admissible counterexamples. The analytic proofs above establish the continuous statements and all-$N$ polygon bound. No floating Sinkhorn experiment is used as a proof.

The verifier checks the seal, frozen original briefs and reports, unchanged reused dependencies, all corpus hashes/Git blobs/pinned URLs, source contracts, actual read-passage hashes, fresh primary response bytes and exact diagnostic output. Live shared-ledger/task-status drift is reported separately from frozen integrity; other mathematical dependency drift is an error. It does not rewrite prior artifacts or regenerate shared results. Integrity verification and deterministic arithmetic do not constitute independent full-proof or significance review.
