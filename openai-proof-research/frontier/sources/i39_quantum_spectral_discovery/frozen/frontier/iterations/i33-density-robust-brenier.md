# I33 — density-robust Brenier stability: a realized obstruction and an atom-count gap

**Disposition.** The requested estimate, uniform over all bounded positive source densities and all targets in a fixed compact set, remains unproved and is not refuted here. The proposed uniform weighted cell-moment estimate is **false**. Section 3 gives an explicit smooth positive density and three actual convex power cells, with exact ratio tending to infinity. It also disproves the corresponding density-uniform linear estimate for normalized potentials. Section 4 investigates a different, direct variational mechanism and identifies its precise limitation. Section 5 proves a technical replacement: the desired cube-root map exponent with a constant depending on the number of atoms, but not their masses, separation, or source derivatives. None of these statements is a substantial-finding nomination or an independent proof-review verdict.

All proofs and internal operations of `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted premises. This report does not audit them. The complete I32 brief, full I32 report, parent verification, prior objections and this follow-up brief are frozen in the assigned source directory. I32's Kerr deduction remains an author-level technical deduction; its logarithmic gap and the other parked tracks are unchanged. No agents, shared-index edits, staging, commits or publication were used.

## 1. Exact question and source contract

Let $d\ge2$, let $K\subset\mathbb R^d$ be compact and convex with nonempty interior, and let $Y\subset\mathbb R^d$ be nonempty and compact. Fix $0<c\le C<\infty$, with $c|K|\le1\le C|K|$. For every measurable probability density $f$ on $K$ satisfying $c\le f\le C$ almost everywhere, write $\rho=f1_K\,dx$. The unproved target is

$$
 \|T_\mu-T_\nu\|_{L^2(\rho)}
 \le A(K,Y,c,C)W_2(\mu,\nu)^{1/3}
 \qquad(\mu,\nu\in\mathcal P(Y)). \tag{Q}
$$

The same constant must work for all such $f$, including smooth densities with unbounded derivative norms. Targets may be atomic or singular. An empty $Y$ gives a vacuous class; a singleton gives identical maps. When the density bounds force $f=1/|K|$, the accepted source already settles the question. The uniform subclass prevents any general improvement of the exponent above $1/3$.

Write BT for *Sharp One-Third Stability of Brenier Maps*, September 25, 2026. All nine text files of BT were read, including the complete proofs in `cells.tex`, `moments.tex`, `finite_stability.tex`, `gradient.tex` and `sharpness.tex`. Their pinned paths, raw URLs, Git blobs and SHA256 hashes are in `source-manifest.json`. The complete 749-manuscript inventory and reused 9340-file text manifest were checked; no truncated root tree or whole-corpus copy was used. The title and text screen found no additional BT density-extension manuscript. This is an inventory/search observation, not a claim that every corpus proof was semantically read.

For distinct sites $y_i$, intercepts $b_i$, and positive cells

$$
 P_i=K\cap\{x:x\cdot y_i+b_i\ge x\cdot y_j+b_j\ \forall j\},
 \quad M_i^f=\int_{P_i}f,\quad B_i^f=\int_{P_i}xf,
$$

the weighted facet coefficients, for smooth $f$, are

$$
 g_{ij}^f=\frac1{|y_i-y_j|}\int_{F_{ij}}f\,dS,
 \qquad b_{ij}^f=\frac1{|y_i-y_j|}\int_{F_{ij}}xf\,dS. \tag{1}
$$

Here the vector coefficient $b_{ij}^f$ is distinct from the scalar intercept $b_i$. Empty or lower-dimensional facets contribute zero. BT's dominated-convergence proof with integrands $f$ and $x_kf$ gives

$$
 DM_i^f[q,0]=\sum_jg_{ij}^f(q_i-q_j),
 \qquad DB_i^f[q,0]=\sum_jb_{ij}^f(q_i-q_j). \tag{2}
$$

The same proof gives joint $C^1$ cell calculus, a connected positive-facet graph, and normalized prescribed-mass intercepts. It uses continuity and positivity of $f$; there is no derivative bound in (1). Connectivity and the null-boundary and tie-plane arguments are geometric and unchanged. Coercivity of the dual objective uses only total source mass one and bounded $K$. These weighted calculus facts are direct source-proof reuse, not the missing estimate.

BT `moments:derivative` gives, for uniform probability,

$$
 \sum_i\frac{|DB_i[q,0]|^2}{M_i}
 \le162R^2\sum_i\frac{|DM_i[q,0]|^2}{M_i},\qquad K\subset B_R. \tag{3}
$$

Its conditional-quantile coupling exactly dominates the midpoint law by the central cell's source measure. The coefficient is one. Testing $R^2-|x|^2$, summing all cells, and cancelling endpoint partition integrals produces a second-order bound. The configuration-dependent permissible perturbation size is harmless after differentiation; the final constant is independent of all cells. For general comparable densities, the crude factor $C/c$ leaves a zeroth-order slack. That observation alone was only a proof failure in I32. Section 3 now supplies an actual counterexample to the proposed weighted replacement of (3).

BT's finite-site argument tests the fixed-mass equation against the Laplacian preimage of $m_i b_i'(t)$, uses (3) to bound the intercept velocity, and obtains a potential estimate linear in $W_2$. Its coordinate-slice interpolation and finite-target limits are already available operations. Two-sided density comparison handles the interpolation; it does not repair (3). Log-concavity would restore exact midpoint domination by the same triangular-Jacobian argument, a technical restricted extension expressly outside the requested contribution gate.

## 2. Early primary comparison and what it actually supplies

Fresh metadata and primary bytes were retrieved on October 9, 2026. The recorded current versions are Letrouit–Mérigot v3, July 16, 2026; Ruan v1, October 6; Wang–Wang v1, October 7; Ford v1, September 28; Divol–Niles-Weed–Pooladian v1; and Bansil–Kitagawa v2. Mérigot's HAL v1 PDF was separately pinned and is byte-identical to the current unversioned retrieval. Exact read ranges, extraction hashes, requests and responses are retained. The operation-level conclusions below use actual proof passages, not abstracts.

* [Letrouit–Mérigot, 2411.04908v3](https://arxiv.org/abs/2411.04908v3), Theorem 2.1, its complete four-step proof, and Proposition 2.2: density comparison with a log-concave reference passes a Brascamp–Lieb variance bound through tilted measures. Integrating the second variation gives a dual-pairing lower bound for the variance of the primal-potential difference. The scaling step replaces the exponential oscillation loss by an explicit diameter factor. This is a variance/coercivity estimate, not the weighted moment-inverse estimate (3). Section 3 below is a direct obstruction to obtaining the latter merely by replacing its source measure with a comparable one.
* [Mérigot, HAL-05616391v1](https://hal.science/hal-05616391v1), Theorem 2.2 and its proof, Theorems 3.1–3.4, and Section 4: quantitative subgradient oscillation controls the fourth power of the map norm by a Jensen/Bregman divergence. In Theorem 3.4, a proximal point converts a feasible plan's correlation gap $G$ into squared map error $E\le C\sqrt G$. This works with a bounded source density; a lower bound is unnecessary. Its map stability has input $W_1$ and exponent $1/4$. The printed dimensional/diameter constants are not needed here; the proof's relevant dependence is on source density and fixed geometry. Section 4 obtains semi-discrete entropic bias of order $\varepsilon^{1/2}$ in map norm using a configuration-dependent quadratic cost-gap asymptotic, not a target-uniform bias assertion.
* [Ruan, 2610.07577v1](https://arxiv.org/abs/2610.07577v1), Section 11's repaired-plan construction and gap proof, and Theorem 8 with proof: $\|T_\mu-T_\nu\|_2\le C W_1(\mu,\nu)^{s/[2(1+s)]}$, $s=1-1/p$, for compact support and $f\in L^p$. At $p=\infty$, this is $W_1^{1/4}$. The proof constants contain the density-size quantity $B_{d,\rho,p}$; the shortened parameter list in the theorem statement does not eliminate it. The $W_r$-repair proposition also gives a gap bounded linearly in $W_2$, hence the same quarter-power by this route. A map norm is not a squared map error, and a feasible-plan gap is not a target distance.
* [Wang–Wang, 2610.09640v1](https://arxiv.org/abs/2610.09640v1), Theorem 1 and the complete Lemmas 6–8/proof: Moreau regularization cancels the first-order averaged Fenchel error. A BV reference density bounds the remaining error by $O(t^2)$, and an $L^p$ weight gives the exponent $(p-1)/(4p-2)$ in $W_2$. Taking the uniform law on $K$ as reference and $h=|K|f$ covers our sources with derivative-free constants but gives $1/4$. This very recent paper explicitly cites BT's uniform-source result. Its sharpness construction uses a fixed source on disconnected rectangles escaping to infinity, so it does not refute (Q).
* [Ford, 2609.35574v1](https://arxiv.org/abs/2609.35574v1), Theorem 4.6 and proof, and the construction in Proposition 5.2: upper Ahlfors regularity gives $W_1^{\theta/[2(1+\theta)]}$ map stability, with $\theta=1$ covering bounded density. Its sharpness uses a density supported on a union of separated rectangles, vanishing elsewhere in a convex container. A convex *container* does not give a positive density throughout that container. The exponent comparison therefore does not settle (Q).
* [Divol–Niles-Weed–Pooladian, 2404.02855v1](https://arxiv.org/abs/2404.02855v1), Proposition 4.1, Theorem 4.3 and their displayed bias/stability proofs: entropic stability plus $O(\varepsilon)$ squared bias gives $W_2^{1/3}$, but the supplied bias constants depend on source regularity and finite-target geometry, masses and atom count. Their remark explicitly identifies a uniform-bias question. The published PDF endpoint returned HTTP 403; the pinned author version was read, and no claim of a full published-version comparison is made.
* [Bansil–Kitagawa, 2002.02022v2](https://arxiv.org/abs/2002.02022v2), Theorem 1.3 and Section 2: acyclicity of the cell-reassignment graph controls changed source mass by changed target masses, with an atom-count factor and no positive-mass or density-regularity assumption. That is precisely the operation reused in Section 5, with a short direct proof for fixed quadratic-cost sites. Their quantitative inverse-potential theorem has additional mass and Poincaré parameters and is not the target-independent inverse bound sought here.

Thus prior art already supplies genuinely density-robust variational machinery. The unresolved distinction is the target-uniform $W_2^{1/3}$ endpoint. Neither a new title for the quarter-power result nor a standard density perturbation of Brascamp–Lieb would settle it. No search absence is used as evidence of novelty.

## 3. Attempt A: the facet graph — an exact smooth obstruction

### 3.1 Construction and all admissibility checks

Work first in $d=2$, $K=[-1,1]^2$, and fix $0<\kappa<1$, for example $\kappa=1/2$. For each $0<a<1/2$, define

$$
 r_a(x)=\frac{2ax}{a^2+x^2},
 \qquad f_a(x,y)=\frac{1+\kappa y r_a(x)}4. \tag{4}
$$

This is a single smooth function for the entire diagram, smooth on a neighborhood of $K$. Since $|r_a|\le1$,

$$
 (1-\kappa)/4\le f_a\le(1+\kappa)/4,
 \qquad \int_K f_a=1. \tag{5}
$$

For $\kappa=1/2$, the same bounds $1/8,3/8$ work for every $a$. The $x$-marginal is exactly uniform on $[-1,1]$; derivatives of $f_a$ are allowed to grow with $a^{-1}$. No singular source measure, disconnected source support, separately assigned facet densities or unrealized graph is involved.

Take sites $(-1,0),(0,0),(1,0)$ and intercepts $(0,a,0)$, i.e.

$$
 u_a(x,y)=\max\{-x,a,x\}.
$$

These are three distinct sites in a fixed compact target set. The cells are the left rectangle $x\le-a$, the middle strip $|x|\le a$, and the right rectangle $x\ge a$, all intersected with $K$. Their masses are

$$
 m_-=(1-a)/2,\qquad m_0=a,\qquad m_+=(1-a)/2. \tag{6}
$$

The only positive facets are $x=-a$ and $x=a$. Since $r_a(\pm a)=\pm1$, their coefficients are exactly

$$
 g_{-0}=g_{0+}=\tfrac12,\quad
 b_{-0}=(-a/2,-\kappa/6),\quad
 b_{0+}=(a/2,\kappa/6). \tag{7}
$$

In particular, **both the scalar Laplacian and the cell masses are identical to those for uniform density**. Only the tangential facet moments have changed. This defeats not just a careless noncommuting Loewner comparison, but any inference using only those scalar operators and masses.

### 3.2 The weighted moment quotient diverges

For the intercept direction $q=(-1,0,1)$, (2) gives

$$
 DM[q,0]=(-1/2,0,1/2),
$$
$$
 DB[q,0]=\bigl((a/2,\kappa/6),,(-a,-\kappa/3),\,(a/2,\kappa/6)\bigr). \tag{8}
$$

Both sums vanish, as required by conservation. Direct substitution yields

$$
 E_M:=\sum_i\frac{|DM_i|^2}{m_i}=\frac1{1-a},
 \quad E_B:=\sum_i\frac{|DB_i|^2}{m_i}
 =\frac{a^2+\kappa^2/9}{a(1-a)},
$$
$$
 \boxed{\frac{E_B}{E_M}=a+\frac{\kappa^2}{9a}\longrightarrow\infty.} \tag{9}
$$

This disproves the suggested bound $E_B\le C(K,c,C)E_M$, even for three noncoalescing sites. Equal incoming and outgoing mass fluxes cancel in the thin cell; their tangential first moments do not. Dividing the residual moment by its small mass causes the divergence. The contrast can be arbitrarily close to one: every fixed $\kappa>0$ still gives divergence. Thus small $L^\infty$ perturbation of uniform density alone does not rescue this operator estimate.

For every fixed $d>2$, use $K=[-1,1]^d$, multiply (4) by $2^{-(d-2)}$, and use sites $-e_1,0,e_1$. The extra coordinates integrate out and (6)–(9) are unchanged. Multiplying all three sites and intercepts by any $\lambda>0$ leaves the cells unchanged and multiplies both derivatives in (8) by $\lambda^{-1}$ when $q$ is held fixed. The ratio is unchanged. The obstruction therefore also persists through coalescing sites.

### 3.3 Exact midpoint domination itself fails

This can be seen before taking a derivative. The middle cells under the opposite perturbations $\pm s q$ are strips centered at $\mp s$, each of width $2a$, for $0<s<1-a$. Their masses are exactly $a$. Let $X,Z$ have the normalized $f_a$-laws on those strips. If

$$
 a\operatorname{Law}((X+Z)/2)\le f_a1_{\{|x|\le a\}}\,dx\,dy, \tag{10}
$$

then equality of total masses forces equality of measures. Under the central law,

$$
 \mathbb E(x^2+y^2)=a^2/3+1/3,
$$

whereas the two endpoint expectations are $a^2/3+s^2+1/3$. The parallelogram identity would therefore force $\mathbb E|X-Z|^2=4s^2$. Their $x$-means already differ by $2s$. Their $y$-means also differ: the mean in the strip centered at $-s$ is

$$
 \frac\kappa6\log\frac{a^2+(a-s)^2}{a^2+(a+s)^2}\ne0, \tag{11}
$$

and the other mean is its negative. Consequently

$$
 \mathbb E|X-Z|^2\ge|\mathbb EX-\mathbb EZ|^2>4s^2,
$$

contradicting (10). This rules out *every* coupling with the exact domination property, not just the triangular coupling. The argument uses the actual smooth density and actual perturbed cells. A compensation scheme must therefore change the source mechanism materially; it cannot simply choose a better coupling satisfying (10).

### 3.4 The stronger potential estimate also fails, modulo all constants

Keep the masses (6), move only the middle site from $0$ to $te_2$, and choose prescribed-mass intercepts $c_i(t)$ with $\sum_i m_ic_i(t)=0$. At $t=0$, subtracting $a^2$ from all the original intercepts realizes this normalization. The weighted cell calculus and implicit function theorem give a $C^1$ path near zero. Differentiating the left and right mass equations using (7) gives

$$
 c_-'(0)-c_0'(0)=-\kappa/3,\quad
 c_+'(0)-c_0'(0)=\kappa/3.
$$

Normalization implies $c_0'(0)=0$. The potential derivative off the null facets is

$$
 h_a(x,y)=
 \begin{cases}
 -\kappa/3,&x<-a,\\
 y,&|x|<a,\\
 \kappa/3,&x>a.
 \end{cases} \tag{12}
$$

For each fixed $a$, local $C^1$ bounds on the intercepts and bounded $K$ dominate the difference quotients of the maximum. Hence they converge to (12) in $L^2(f_a)$. Its mean is zero, and

$$
 \operatorname{Var}_{f_a}(h_a)=(1-a)\kappa^2/9+a/3. \tag{13}
$$

The target laws are exactly

$$
 \mu_a=\tfrac{1-a}2(\delta_{-e_1}+\delta_{e_1})+a\delta_0,\quad
 \nu_{a,t}=\tfrac{1-a}2(\delta_{-e_1}+\delta_{e_1})+a\delta_{te_2}.
$$

Matching corresponding atoms has squared cost $at^2$, and projection onto the second target coordinate gives the same lower bound for every coupling. Thus $W_2=\sqrt a,|t|$. Since subtracting the best additive constant is exactly taking variance,

$$
 \lim_{t\to0}\frac{\inf_k\|u_{a,t}-u_{a,0}-k\|_{L^2(f_a)}}{W_2(\mu_a,\nu_{a,t})}
 =\sqrt{\frac{(1-a)\kappa^2/9+a/3}{a}}\longrightarrow\infty. \tag{14}
$$

All potentials for a fixed optimal map on this full-support convex source differ by constants, so choosing a different potential normalization cannot avoid (14). The limit in $t$ is taken first for each fixed positive $a$, followed by $a\downarrow0$; no uniform implicit-function neighborhood is asserted.

### 3.5 Why this is not a counterexample to (Q)

The map discrepancy in the small-$t$ regime is caused by boundary reassignment of order $|t|$ in source mass, hence typically has norm of order $|t|^{1/2}$, whereas the target distance is $\sqrt a,|t|$. Their cube-root ratio has the scale $(|t|/a)^{1/6}$. The local derivative argument only applies for sufficiently small $t$ at fixed $a$; it gives no divergence of this ratio.

There is also a rigorous large-tilt mass constraint. Write a normalized tilted maximum as

$$
 \max\{-x+z,,A+ty,\,x-z\},
$$

allowing the middle width $(A+ty)_+$ to vanish on some horizontal slices. The left and right outer atoms are separated by $x=z$ whenever the middle atom is absent. With fixed left mass $(1-a)/2$ and middle mass $a$, the uniform $x$-marginal implies $|z|\le a$: the mass of ${x<z}$ differs from the left mass by a number in $[0,a]$. Source points receiving different outer labels must lie between $x=0$ and $x=z$. Together with the two middle cells, the mass of points changing their first target coordinate is at most $3a$. Therefore, for $|t|\le1$,

$$
 \|T_{\mu_a}-T_{\nu_{a,t}}\|_2^2\le12a+at^2. \tag{15}
$$

In particular, $|t|\ge a$ also cannot make the cube-root ratio diverge. Section 5 supplies a uniform three-atom cube-root estimate covering the intermediate regime. The construction conclusively rejects the moment and linear-potential routes; it does not reject (Q).

## 4. Attempt B: compensated regularization and direct variational control

### 4.1 The derivative-free second-order cancellation is already available

Let $u$ be a globally convex $L$-Lipschitz potential and

$$
 u_t(x)=\inf_z\{u(z)+|x-z|^2/(2t)\},\quad
 a_t=u_t-u+\tfrac t2|\nabla u|^2.
$$

The conjugacy identity $u_t^*=u^*+t|\cdot|^2/2$ gives $a_t\ge0$ and, on a fixed-marginal plan, an averaged Fenchel-gap increase $A_t=\int a_tf$. The Wang–Wang proof supplies

$$
 \int_K a_t\frac{dx}{|K|}\le \frac{L^3\operatorname{Per}(K)}{6|K|}t^2,
 \qquad A_t\le \frac{CL^3\operatorname{Per}(K)}6t^2. \tag{16}
$$

Convex bodies have finite perimeter, including nonsmooth ones. Crucially, positivity allows comparison of the *already compensated* nonnegative gap with uniform measure. No derivative of $f$ appears. This genuinely removes the zeroth-order density slack, but it is a known operation and it estimates a different quantity from cell moments.

Coercivity of the $1/t$-Lipschitz regularized gradient and a repaired target coupling give, with $D=\|T_\mu-T_\nu\|_2$, $w=W_2(\mu,\nu)$, and a geometry-dependent constant,

$$
 (D-w)_+^2\le C_1 w/t+C_2t. \tag{17}
$$

The repair step glues the two optimal source-target plans to a $W_2$-optimal target coupling and bounds the correlation gap by

$$
 G\le\mathbb E\langle X_\mu-X_\nu,Y_\mu-Y_\nu\rangle
 \le2M_\rho w.
$$

Optimizing (17) gives $D\lesssim w^{1/4}+w$, not $w^{1/3}$. The obstruction is now the treatment of the correlation gap and the relation between source positions under the glued coupling; it is not failure to compensate density at order zero.

### 4.2 Two exact tests block simple exponent upgrades

First, the $t^2$ in (16) cannot universally be improved to $t^3$. For the uniform law on the cube and $u(x)=|x_1|$, for $0<t<1$,

$$
 a_t(x)=\frac{(t-|x_1|)^2}{2t}1_{\{|x_1|<t\}},
 \qquad \int a_t\,d\rho=t^2/6. \tag{18}
$$

Second, generic plan conditioning cannot improve from $E\le C\sqrt G$ to $E\le CG^{2/3}$, even on a uniform convex source. Let $T(x)=\operatorname{sign}(x_1)e_1$, transporting the uniform cube to the two equal outer atoms. On $|x_1|\le h$, reverse the sign to form $S_h$; elsewhere keep $T$. Symmetry makes $S_h$ feasible for the same target. Exact integration gives

$$
 E_h=\int|S_h-T|^2\,d\rho=4h,
 \qquad G_h=\int x\cdot(T-S_h)\,d\rho=h^2. \tag{19}
$$

Thus $E_h=4\sqrt{G_h}$. This is a genuine feasible transport plan, but it is not the plan obtained by repairing the identity target coupling when the targets coincide. It blocks a generic conditioning upgrade, not an estimate using the special structure of two optimal maps.

A conceivable improvement would control that special repair gap more strongly, or retain source/target cancellation before Cauchy–Schwarz. No such bound is proved here. In particular, neither $\|X_\mu-X_\nu\|_2\lesssim D$ for a chosen gluing nor a bound $D^3\lesssim w$ is inserted as a hypothesis. The conditional source laws over atoms can be diffuse; choosing an arbitrary independent gluing loses information. A correct proof must build and estimate a suitable gluing, not identify it with the common-source coupling, which generally is not optimal between the targets.

### 4.3 Entropic variant: another precise unpaid estimate

The entropic approach supplies stability roughly proportional to $w/\varepsilon$ on fixed bounded supports. A squared bias $\|T^\varepsilon_\mu-T_\mu\|_2^2\lesssim\varepsilon$, uniformly over all targets and all our densities, would give $D^2\lesssim\varepsilon+w^2/\varepsilon^2$, and hence the desired exponent. The cited semi-discrete proof pays for that bias with configuration-dependent dual-potential and interface estimates. Mérigot's general plan conditioning alone only turns a cost gap into its square root. Neither source establishes the required target-uniform bias for this class.

This route avoids the false moment estimate, but replacing its bias constant by a uniform one is a mathematical gap, not a completed reduction counted as a result. The thin-cell example does not itself disprove that bias bound. No interchange of a fixed-configuration entropic asymptotic with growing atom count or vanishing masses is made.

## 5. A proved technical replacement with an explicit atom-count loss

The following author proof retains a useful part of the target without pretending its constant is uniform in the number of atoms. Its ingredients are elementary graph maximum principles, the already-known acyclic reassignment mechanism, and convex one-dimensional integration by parts. These are reasons to classify it as technical, irrespective of whether this exact packaged statement is printed elsewhere.

**Finite-target proposition.** Fix $K\subset B_R(0)$, $Y\subset B_L(0)$, with $R,L\ge1$, and set

$$
 P_K=\sum_{j=1}^d|\operatorname{proj}_{e_j^\perp}K|_{d-1}.
$$

Let $c\le f\le C$ be any measurable probability density on $K$. If $\mu,\nu\$ have at most $n,m$ positive atoms, put $N=nm$. Then

$$
 \boxed{\|T_\mu-T_\nu\|_{L^2(f)}^2
 \le(2N-1)(16CLP_KR+8L^2)W_2(\mu,\nu)^{2/3}.} \tag{20}
$$

One can use the number of positive pairs in a chosen optimal target coupling in place of $nm$. No minimum-mass, site-separation, angle, or density-derivative parameter occurs. The factor in $N$ is not claimed sharp.

### 5.1 A bounded site-speed estimate

Initially assume $f$ smooth and positive. Fix positive labelled masses $m_i$, and affine site paths $y_i(t)$ with $|y_i'|\le\eta$. Merge any pairs whose entire paths coincide. On each open interval between collision times, prescribe these masses using intercepts $c_i(t)$, normalized by $\sum_i m_ic_i(t)=0$, and write $r_i=c_i'(t)$. There are only finitely many collision times: two distinct affine paths coincide at at most one time.

At each regular time, differentiating the masses gives

$$
 0=\sum_jg_{ij}\{r_i-r_j+\bar x_{ij}\cdot(v_i-v_j)\},
 \quad \bar x_{ij}=b_{ij}/g_{ij}\in K. \tag{21}
$$

Sort the $r_i$. If a consecutive gap exceeded $2R\eta$, sum (21) over all vertices above that gap. Internal edges cancel. Every crossing edge contributes strictly positively, since $|\bar x_{ij}\cdot(v_i-v_j)|\le2R\eta$. Connectivity guarantees at least one such edge, a contradiction. Hence

$$
 \operatorname{osc}r\le2R(N-1)\eta,\qquad
 \max_i|r_i|\le2R(N-1)\eta. \tag{22}
$$

The second inequality uses the weighted zero mean, not a lower bound on any mass. For the finite maximum $u_t$, its time derivative on a strict active cell is $x\cdot v_i+r_i$. Thus

$$
 \|\partial_tu_t\|_\infty\le R(2N-1)\eta. \tag{23}
$$

At a collision, (22) gives finite one-sided limits of every intercept. A label of positive prescribed mass cannot have a strictly smaller limiting intercept than another label with the same limiting slope: it would be strictly inactive on all of $K$ near the collision. Repeated slopes therefore merge with equal intercepts. The limiting convex maximum has the correct collapsed target law, as in BT's endpoint proof. The two limiting maxima define the same unique optimal map. Because $f\ge c>0$ and the interior of $K$ is connected, two convex Lipschitz functions with this same gradient differ by a constant. Their positive-mass supporting affine coefficients then differ by this same constant; normalization forces it to be zero. Therefore the maxima and normalized intercepts join across the collision. Integrating (23) over the finitely many intervals proves

$$
 \inf_k\|u_1-u_0-k\|_\infty\le R(2N-1)\eta. \tag{24}
$$

This works for any bounded-displacement labelled target coupling, not only an optimal coupling. In particular the possibly nonoptimal partial movement in Section 5.3 is allowed. Persistent coincidences are merged first; endpoint coincidences are handled by the same argument. For $N=1$, the intercept is zero and (23) is immediate.

### 5.2 Two elementary conversion estimates

For two convex $L$-Lipschitz functions $u,v$ on $K$, let $w=u-v-k$. On almost every coordinate interval, $w'$ is bounded by $2L$ and has total variation at most $4L$. Integration by parts for this BV derivative gives

$$
 \int (w')^2\le8L\|w\|_\infty.
$$

Indeed, the two endpoint products cost at most $4L\|w\|_\infty$, and the integral of $w\,d(w')$ costs at most another $4L\|w\|_\infty$. One-sided endpoint traces exist for convex functions. Fubini over coordinate slices, followed by $f\le C$, gives

$$
 \|\nabla u-\nabla v\|_{L^2(f)}^2\le8CLP_K\inf_k\|u-v-k\|_\infty. \tag{25}
$$

Next, suppose two target laws use the same set of $k\ge2$ distinct sites in $Y$, permitting zero masses. For intercepts $c,d$, let $F_{ij}\ge0$ be the source mass assigned to site $i$ by the first map and site $j\ne i$ by the second. Off the null tie sets, both maximizing inequalities are strict, so $F_{ij}>0$ implies

$$
 d_j-c_j>d_i-c_i.
$$

The transfer graph is acyclic. Its divergence is the difference of target masses. Decompose its flow into paths from vertices with net outgoing mass to vertices with net incoming mass: a finite greedy subtraction along paths terminates since there are no cycles. Total path weight is the total variation distance $\beta=\frac12\sum_i|m_i-n_i|$; each path has at most $k-1$ edges. Consequently

$$
 \sum_{i\ne j}F_{ij}\le(k-1)\beta,\qquad
 \|T_m-T_n\|_2^2\le4L^2(k-1)\beta. \tag{26}
$$

Absent sites can be given intercepts sufficiently negative to be strictly inactive throughout $K$, so zero masses cause no difficulty. This is the fixed-quadratic-cost form of the Bansil–Kitagawa acyclic reassignment argument, not a new target-uniform estimate. If $k=1$, both maps agree.

### 5.3 Slow movements, small exceptional mass, and the cube-root exponent

Take an optimal finite coupling

$$
 \pi=\sum_{i=1}^{N'}m_i\delta_{(y_i,z_i)},\quad m_i>0,\quad
 \sum_i m_i|y_i-z_i|^2=w^2,\quad N'\le nm.
$$

For $\eta>0$, form an intermediate law $\lambda$: move pair $i$ from $y_i$ to $z_i$ when $|y_i-z_i|\le\eta$; otherwise leave it at $y_i$. Its labelled movement has speed at most $\eta$, so (24)–(25) give

$$
 \|T_\mu-T_\lambda\|_2^2
 \le8CLP_KR(2N'-1)\eta. \tag{27}
$$

The mass of the remaining pairs is at most $w^2/\eta^2$. Thus $d_{TV}(\lambda,\nu)\le w^2/\eta^2$; their common site union has at most $2N'$ sites. Equation (26) gives

$$
 \|T_\lambda-T_\nu\|_2^2\le4L^2(2N'-1)w^2/\eta^2. \tag{28}
$$

The squared triangle inequality and $\eta=w^{2/3}$, for $w>0$, prove (20). There is no need to suppose $w\le1$. For $w=0$, uniqueness gives identical maps. Intermediate affine paths remain in $B_L$; they need not remain in the nonconvex set $Y$. Their endpoints and all intermediate *laws* used in (27)–(28) are supported in $Y$.

### 5.4 Measurable source densities and limiting order

The passage to measurable $f$ is not assumed. Extend $f$ by a value in $[c,C]$ outside $K$ and convolve with smooth nonnegative mollifiers, obtaining smooth $h_j\in[c,C]$ and $h_j\to f$ in $L^1(K)$. Put $I_j=\int_K h_j\to1$. If $I_j>1$, mix $h_j$ with the constant $c$, using weight $(I_j-1)/(I_j-c|K|)$. If $I_j<1$, mix with the constant $C$, using weight $(1-I_j)/(C|K|-I_j)$. This produces smooth probability densities $f_j\in[c,C]$ with $f_j\to f$ in $L^1(K)$. When $c|K|=1$ or $C|K|=1$, $f$ is the forced constant density and no approximation is needed.

Fix a target $\lambda\in\mathcal P(Y)$. For smooth positive source and finite target, the weighted prescribed-mass construction gives its potential. For a general compact target, first take finite nets and apply the compactness, gradient-convergence and Fenchel argument below with the source fixed; this constructs the potential without assuming a quantitative bound uniform in atom count. Normalize the $L$-Lipschitz convex potentials for source $f_j$ at a point of $K$. By Arzelà–Ascoli, every subsequence has a uniformly convergent further subsequence with convex limit $u$. At every interior differentiability point of $u$ where all the approximating gradients exist, the supporting inequalities at $x\pm he_k$, followed first by $j\to\infty$ and then $h\downarrow0$, show $\nabla u_j(x)\to\nabla u(x)$. The excluded set is Lebesgue null, hence null for all these sources. The boundary of $K$ is null.

Bounded slopes and $L^1$ convergence of the densities show $(\nabla u)_\#(f\,dx)=\lambda$: test continuous functions of the slopes, replace $f_j$ by $f$ with an $L^1$ error, and use dominated convergence. Since $Y$ is closed, the limiting gradients lie in $Y$ almost everywhere. Supporting inequalities and the restricted Fenchel conjugate on $K$ prove optimality and uniqueness exactly as in BT. Thus the limit is $T^f_\lambda$, and every such subsequence has this same limit. Dominated convergence yields full-sequence strong $L^2(f)$ convergence of the maps.

Apply this separately to the two fixed finite targets. Changing the norm's density from $f_j$ to $f$ costs at most $4L^2\|f_j-f\|_1$ in squared map distance. Hence (20) passes with the same constant. Limits are taken with the target pair and atom counts fixed, then with $j\to\infty$. The argument also proves qualitative convergence for compactly supported varying targets by the same supporting-inequality proof. It does **not** remove the factor $N$ when finite nets grow.

## 6. Adversarial checks and the remaining gap

The exact counterexample (4) is smooth, bounded above and below, supported throughout a convex cube, and uses one common density for all facets. It has a thin positive-mass cell, exact scalar-flux cancellation, and no cycle. Scaling sites realizes coalescence. It already refutes the sufficient estimate in the smallest relevant three-cell setting; large graph artifacts are unnecessary for that conclusion.

The deterministic rational experiment additionally builds actual power diagrams: square grids with four and nine sites, a six-site ring with a central site and cycles, thin strips, and scaled/coalescing strip sites. Polynomial densities $f=(1+\tfrac12yT_k(x))/4$, $k=1,3,7$, are positive with the same fixed bounds, since $T_k$ is the Chebyshev polynomial on $[-1,1]$. All cell, facet, mass, first-moment and polygon-intersection integrals are exact rational values. Actual target laws are computed from the gradients; exact rational min-cost flow computes $W_2^2$ for 18 perturbed-diagram pairs, and intersections compute their squared map distance. These tests include changing atom counts, cycles, oscillatory densities, coalescing sites and zero-cell handling. They do not establish a uniform inequality or a counterexample sequence to (Q).

The separate fixed-mass three-site search solves the tilted-strip mass constraints numerically for 15 $(a,t)$ pairs, including $t\ll a$, $t\approx a$, and $t\gg a$. Its quadrature is explicitly not certified. The largest difference between the two quadrature grids in squared map error was below $8\times10^{-7}$; the largest cube-root diagnostic $D^6/W_2^2$ was approximately $0.117$. These finite observations are consistent with, and superseded for this fixed-atom family by, (20). They are not evidence that (Q) holds for unbounded atom count.

What remains is now narrower than the I32 screen: a weighted analogue of (3), or even the linear-potential conclusion it was intended to prove, cannot be the general answer. A successful target-uniform proof would need a different quantity, a compensated comparison of two optimal maps, a genuinely uniform entropic bias, or another mechanism controlling many-cell reassignment without paying one unit for every possible intermediate cell. The graph and variational attempts here fail at different identified interfaces. The atom-count factor in (20) is a proof loss, not an established obstruction to (Q).

The restricted theorem is not promoted merely because it tolerates nonsmooth densities or degenerate targets. The cell calculus, maximum principle, acyclic transfer and interpolation are standard/source operations. No complete literature-priority claim is made for either its packaging or the obstruction. Independent proof and significance review would still be needed before any accepted finding; this report makes no count change.

## 7. Reproduction and evidence boundaries

Run from the project root:

```bash
python frontier/experiments/i33_density_robust_brenier/diagnostics.py
python frontier/experiments/i33_density_robust_brenier/fixed_mass_search.py
python frontier/experiments/i33_density_robust_brenier/verify.py
```

The first command verifies 45 exact closed-form parameter cases, 128 directed-flow cases, 90 nonzero facet-energy cases and 18 exact transport comparisons, plus exact conditioning/Moreau identities. The second is a bounded floating diagnostic, not a proof. The third verifies frozen inputs, source Git/SHA identities, the entire reused corpus, read-passage hashes, primary-response/extraction bytes, and the artifact seal; live shared-input drift is reported separately.

The read log identifies passages actually opened. Hashing every corpus file is not reading every proof. The first exploratory web response was not serialized; this is documented rather than replaced by a purported identical response. Later search requests and responses are retained. One nominal published PDF returned a 212-byte HTML challenge with HTTP 200, and another returned HTTP 403; these bytes and their failure classification are retained. Successful Bansil–Kitagawa arXiv v2 and NSF publication bytes were then fetched. No failure is disguised as a read paper, and no unexamined primary text is a mathematical dependency.

The final handoff is a scoped obstruction plus a developed gap and technical finite-atom replacement. Shared ledgers and previous reports remain untouched; parent integration and any separately authorized project-only publication remain outside this task.
