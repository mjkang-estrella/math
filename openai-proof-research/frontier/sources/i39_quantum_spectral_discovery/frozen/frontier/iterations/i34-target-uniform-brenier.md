# I34 — target-uniform Brenier stability: audit, geometric costs, and entropic normalization

**Disposition.** Q remains **unproved and not refuted**. The original I33 obstruction and finite-target proposition pass the independent mathematical audit below, without a mathematical repair. This is an audit of I33's deductions, not an audit of the stipulated OpenAI corpus. The constructive work develops two different routes beyond the false moment inequality. It produces an actual many-cell zigzag realization, a constructed optimal-target gluing and a counterexample to one proposed estimate for it, a target-uniform entropic conditional-variance bound, a genuine uniform two-atom bias theorem, and a configurationwise bias estimate with a uniform limiting coefficient. None closes the many-atom bias or weighted reassignment estimate needed for Q. A growing-cluster example rigorously rejects a uniform norm bound on the individual counting-measure dual corrections; it does **not** reject uniform map bias.

The statements proved here are technical deductions or obstructions to specified proof shortcuts. They are not a substantial-theorem nomination. Any eventual affirmative theorem still needs a fresh full-proof review and separate significance review. Original reports, sources, shared indexes and previous artifacts are unchanged. No agents, staging, commits or publication were used.

## 1. Scope, conventions, and the independent I33 audit

Fix a compact convex body $K\subset\mathbb R^d$, $d\ge2$, a compact nonempty $Y$, and $0<c\le C$ with $c|K|\le1\le C|K|$. Sources are all probabilities $\rho=f1_K dx$, $c\le f\le C$ a.e. Put $K\subset B_R$, $Y\subset B_L$, choosing $R,L\ge1$, and

$$P_K=\sum_{j=1}^d|\operatorname{proj}_{e_j^\perp}K|_{d-1},\quad
D=\|T_\mu-T_\nu\|_{L^2(\rho)},\quad w=W_2(\mu,\nu).$$

Q asks for $D\le A(K,Y,c,C)w^{1/3}$ simultaneously for all sources and targets, without bounds on derivatives, atom count, masses or separations. The constant-source subclass already rules out exponents greater than $1/3$. All BT proof operations at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are premises. All nine BT text files were read, including the complete cell, moment, finite-target, interpolation, approximation and sharpness interfaces. The complete tree and catalogue were used; the 9340-file corpus was reused read-only. Inventory/hash verification is not a claim to have read every manuscript.

### 1.1 Original obstruction: PASS, with the order of limits retained

For $K=[-1,1]^2$, $0<a<1/2$, fixed $0<\kappa<1$, write

$$f_a(x,y)=\tfrac14\left(1+\kappa y\frac{2ax}{a^2+x^2}\right),\qquad
u_a(x,y)=\max(-x,a,x).$$

The rational factor has absolute value at most one, the density is smooth on a neighborhood of $K$, and integrating in $y$ gives the constant marginal $1/2$. Consequently the masses are $((1-a)/2,a,(1-a)/2)$, and the two scalar facet coefficients are $1/2$. Integration of $xf_a,yf_a$ on $x=\pm a$, divided by the unit site separation, gives

$$b_{-0}=(-a/2,-\kappa/6),\qquad b_{0+}=(a/2,\kappa/6).$$

For $q=(-1,0,1)$, mass derivatives are $(-1/2,0,1/2)$; moment derivatives are $((a/2,\kappa/6),(-a,-\kappa/3),(a/2,\kappa/6))$. Their weighted squared-energy quotient is exactly

$$a+\frac{\kappa^2}{9a}.$$

The scalar operator and masses really are unchanged from uniform density. This is a realized smooth counterexample to the weighted moment estimate, not merely a noncommutation concern.

For opposite intercept perturbations, the middle strips have mass $a$, centers $\mp s$, and equal width $2a$. Exact midpoint domination would be equality because the measures have equal total mass. Integrating $|x|^2$ against that equality forces the squared source displacement to be $4s^2$. The horizontal means alone already use $4s^2$, and the two vertical means differ by twice

$$\frac\kappa6\log\frac{a^2+(a-s)^2}{a^2+(a+s)^2}\ne0.$$

Jensen's inequality then contradicts the forced displacement. This excludes every such midpoint coupling.

The fixed-mass site path moving the middle site to $te_2$ is legitimate for each fixed $a>0$. BT's cell derivative proof already permits continuous integrands: substituting $f_a$ and coordinate times $f_a$ gives joint $C^1$ masses. Positivity preserves the connected facet graph, hence the mass Jacobian restricted to the weighted-mean-zero hyperplane is invertible. The implicit function theorem supplies the local path. Its intercept derivatives are $(-\kappa/3,0,\kappa/3)$. Difference quotients of the maximum converge in $L^2(f_a)$, because a local $C^1$ bound supplies a dominating constant and ties are null. The derivative is

$$h_a=(-\kappa/3)1_{x<-a}+y1_{|x|<a}+(\kappa/3)1_{x>a},\qquad
\int h_af_a=0,$$
$$\operatorname{Var}_{f_a}h_a=(1-a)\kappa^2/9+a/3.$$

The vertical target projection supplies the lower bound $at^2$ for every coupling; corresponding-atom matching attains it. Thus $w=\sqrt a|t|$. Subtracting *any* best constant is exactly taking variance. Equal gradients on the connected interior of $K$ imply equality of potentials modulo constants, since these potentials are Lipschitz and $f_a\ge c>0$. There is no alternative normalization that evades the divergence. The limit is $t\to0$ at fixed $a$, then $a\downarrow0$. No joint limit or uniform implicit-function neighborhood follows.

For the large-tilt check, write the potential as

$$\max\{-x+z,A+ty,x-z\}.$$

Positive outer masses force $-1<z<1$. The left cell is contained in $\{x<z\}$; its complement there is a subset of the middle cell. Therefore

$$0\le\rho(x<z)-(1-a)/2=(z+a)/2\le a,$$

so $|z|\le a$, including horizontal slices where the middle cell is absent or clipped. A direct outer-to-outer reassignment can occur only between $x=0$ and $x=z$. Adding both middle cells bounds changed first-coordinate mass by $3a$ (the estimate is deliberately loose). Thus $D^2\le12a+at^2$ for $|t|\le1$. This is an upper bound, and does not turn the divergent derivative into a counterexample to Q.

**Original verdict:** PASS for I33 §§3.1–3.5. The historical doubled commas and stray typesetting symbols do not alter these computations. They are not silently corrected in the frozen original.

### 1.2 Original finite-atom proposition: PASS, without an omitted collision hypothesis

Here is a reconstruction of the proof interfaces, including the potentially delicate steps. For positive fixed masses $m_i$, distinct sites and smooth positive $f$, minimize

$$\mathcal F(b)=\int_K\max_i(x\cdot y_i+b_i)f(x)dx-\sum_i m_ib_i
\quad\text{on }\sum_i m_ib_i=0.$$

The lower bound $\mathcal F(b)\ge\max_i b_i-R\max_i|y_i|$ proves coercivity for each positive mass vector. The gradient is $M-m$. A constrained critical point has $M-m\in\operatorname{span}(m)$; summing its coordinates gives zero, so $M=m$. The weighted version of BT's facet calculus gives a connected graph and kernel consisting of constants. The restricted Jacobian is invertible. Local uniqueness plus convexity of $\mathcal F$ gives global uniqueness and $C^1$ dependence on distinct sites. This does not estimate an inverse operator uniformly.

For affine paths of speed at most $\eta$, let $r_i=b_i'$. The fixed-mass equations are

$$0=\sum_jg_{ij}\{r_i-r_j+\bar x_{ij}\cdot(v_i-v_j)\},\qquad
\bar x_{ij}\in K.$$

If a consecutive gap in the ordered $r_i$'s exceeds $2R\eta$, summing over the upper block makes every crossing contribution positive; connectivity makes at least one strictly positive. Hence

$$\operatorname{osc}r\le2R(N-1)\eta,\quad
\max_i|r_i|\le2R(N-1)\eta,\quad
\|\partial_tu_t\|_\infty\le R(2N-1)\eta.$$

The middle inequality uses $\sum m_ir_i=0$, not a minimum mass. Persistent identical affine site paths can be merged, adding their masses; all other pairs have at most one collision time. The displayed derivative bound gives finite one-sided intercept limits at every remaining collision. Two colliding labels of positive mass must have equal limiting intercepts: otherwise the smaller affine function is uniformly dominated on $K$ near the collision and its prescribed positive cell mass disappears. Merging each collision group gives a limiting maximum with the collapsed target law, by convergence off the finitely many distinct-slope tie planes. The maxima on the two sides induce the same unique optimal map, so differ by a constant on $K$. For each positive collapsed cell the active affine coefficient differs by this constant. Weighted normalization makes the constant zero. Thus the paths join. This argument also handles repeated endpoint slopes and does not require the partially moved coupling to be optimal.

On each coordinate interval, for $w=u-v-k$, integration by parts for the BV function $w'$ gives

$$\int(w')^2\le 8L\|w\|_\infty.$$

The two boundary terms cost at most $4L\|w\|_\infty$; the difference of two monotone derivatives has variation at most $4L$. Slicing and $f\le C$ yield

$$\|\nabla u-\nabla v\|_{L^2(f)}^2\le8CLP_K\inf_k\|u-v-k\|_\infty.\tag{1}$$

For two measures on the same $k$ distinct sites, let $F_{ij}$ be the source mass moving from $i$ to $j$. If their intercept vectors are $b,d$, positive $F_{ij}$ implies $d_j-b_j>d_i-b_i$: add the two strict active-cell inequalities. Thus the flow is acyclic. Attach a source to vertices of positive net outflow and a sink to vertices of positive net inflow. Conservation at the remaining vertices and acyclicity allow decomposition into source-to-sink paths. Their total weight is $\beta=d_{TV}(m,n)$, and each has at most $k-1$ edges. Therefore

$$\sum_{i\ne j}F_{ij}\le(k-1)\beta,\qquad
\|T_m-T_n\|_2^2\le4L^2(k-1)\beta.\tag{2}$$

Zero-mass sites are harmless: represent the positive-site optimum and give every absent site an intercept strictly below the minimum needed to be active anywhere on compact $K$. No lower bound on masses was inserted. The graph operation is already present in Bansil–Kitagawa; (2) is its elementary quadratic-cost specialization.

Now take a finite optimal target coupling with $N$ positive pairs. Move pairs of length at most $\eta$, leaving the others fixed, to obtain $\lambda$. Equations (1) and the site-speed bound give

$$\|T_\mu-T_\lambda\|_2^2\le8CLP_KR(2N-1)\eta.$$

The remaining mass is at most $w^2/\eta^2$. The site union of $\lambda,\nu$ has at most $2N$ elements, so (2) bounds the other squared map difference by $4L^2(2N-1)w^2/\eta^2$. Multiplying both estimates by two for the squared triangle inequality and choosing $\eta=w^{2/3}$ proves exactly I33's constant:

$$D^2\le(2N-1)(16CLP_KR+8L^2)w^{2/3}.\tag{3}$$

For $w=0$, uniqueness applies. For $N=1$, all intercept derivatives vanish. The moving slopes stay in $B_L$; no convexity of $Y$ is assumed. The auxiliary endpoint laws in the splitting are supported in $Y$.

For measurable sources, extend $f$ outside $K$ by a value in $[c,C]$, mollify, and correct its integral by mixing with the constant $c$ or $C$. The mixing coefficient tends to zero unless $c|K|=1$ or $C|K|=1$, in which case the only density is constant. Thus the smooth probabilities retain exactly the bounds $c,C$ and converge in $L^1(K)$. Normalized convex potentials have a uniformly convergent subsequence. Supporting inequalities at $x\pm he_j$ give gradient convergence at almost every differentiability point of the limit. Bounded slopes, $L^1$ convergence of the sources and dominated convergence pass the target law to the limit. Restricted Fenchel equality proves optimality and uniqueness. Every subsequence therefore has a further subsequence of maps converging to the same limit in $L^2(f)$, which implies full-sequence convergence. Changing the density in a squared map norm costs at most $4L^2\|f_j-f\|_1$. This proves (3) for measurable $f$, with its original constant.

**Original verdict:** PASS for I33 §5, including all constants, collisions, zero masses, and approximation. This audit does not accept (3) as a substantial contribution. Its atom-count factor survives, so finite-net approximation cannot prove Q.

### 1.3 Prior-art normalization clarification, separate from that PASS

The statement in I33 about configuration-dependent entropic bias remains valid. Its use of the printed unshifted dual convergence estimate in DNWP requires a convention clarification. DNWP writes entropy relative to $\rho\otimes\mu$, while its cited Delalande estimate is for counting measure on the finite target. Section 3 below supplies the precise conversion and an exact two-atom test. No I33 obstruction or proof of (3) depends on that unshifted estimate. The standalone Q remains open after the clarification.

## 2. Constructive route A: retain geometry and squared jump costs

### 2.1 A uniform interface budget is available, but is not a flow bound

For a convex finite maximum $u$ with slopes in $B_L$, the distributional Hessian on internal facets is

$$D^2u\big|_{F_{ij}}=|y_i-y_j|\,n_{ij}\otimes n_{ij}\,\mathcal H^{d-1}\big|_{F_{ij}}.$$

Coordinate slicing gives $\int_K\partial_{jj}u\le2L|\operatorname{proj}_{e_j^\perp}K|$: the derivative on each interval is monotone and lies in $[-L,L]$. Thus

$$\sum_{i<j}|y_i-y_j|\int_{F_{ij}} f\,dS
\le2CLP_K.\tag{4}$$

This is used only for continuous $f$ on facets; for a merely measurable density its a.e. values do not specify a trace. The unweighted BV budget always makes sense. Smooth approximation can be used when a subsequently integrated quantity is stable under $L^1$ convergence; an arbitrary chosen trace is never inserted.

For intercept perturbations $h_i$, the infinitesimal squared jump cost of crossings is

$$\sum_{i<j}|y_i-y_j|\int_{F_{ij}}f\,dS\,|h_i-h_j|.\tag{5}$$

Equation (4) controls (5) if the relevant differences of $h$ are controlled. In a fixed-mass site path the corresponding factor is $|h_i-h_j+x\cdot(v_i-v_j)|$. Neither (4) nor lower density alone bounds those factors by the target quadratic speed. This is exactly where using only the BV budget stops.

### 2.2 A geometrically realized long zigzag, and the conductance it must pay

There is no theorem bounding the sum of squared target jumps along every realized reassignment path by target diameter. Here is an explicit family for every integer $n\ge2$. On $K=[-1,1]^2$, with uniform density $1/4$, take

$$y_j=((-1)^j,j/n),\quad b_j=-\frac{j^2}{2n^2},\quad -n\le j\le n,
\qquad U_n(x,y)=\max_j\{(-1)^jx+(j/n)y+b_j\}.\tag{6}$$

All sites lie in the fixed square $Y=[-1,1]^2$, and all cells have positive mass. At fixed parity, the second-coordinate affine functions are tangents to $y^2/2$. The active interval for an interior index $j$ within its parity is $[(j-1)/n,(j+1)/n]$. Consecutive opposite-parity cells $j,j+1$ share a facet with vertical range $[j/n,(j+1)/n]$; equality gives

$$x=\frac{(-1)^j}{2n}\left(y-\frac{2j+1}{2n}\right).$$

Along that range no other line exceeds the two displayed lines, so these are actual facets, not proposed graph edges. Their lengths are $n^{-1}\sqrt{1+(4n^2)^{-1}}$, while their target jumps have length $2\sqrt{1+(4n^2)^{-1}}$. Hence

$$g_{j,j+1}=\frac1{8n}.$$

Same-parity neighbors $j,j+2$ meet at $y=(j+1)/n$ on the side $(-1)^jx\ge1/(4n^2)$, giving

$$g_{j,j+2}=\frac n8\left(1-\frac1{4n^2}\right),\qquad
\frac{g_{j,j+2}}{g_{j,j+1}}=n^2-\frac14.\tag{7}$$

Perturb intercepts by $t j/n$. This is the actual convex maximum $U_n(x,y+t)$. Each old-to-new reassignment across a consecutive facet goes from $j$ to $j+1$ for sufficiently small positive $t$: their intercept increments are strictly ordered. A compact relative interior portion of each facet is free of triple ties, so a positive-width swept slab proves positive reassignment mass. The actual exchange DAG therefore contains the path $-n,-n+1,\ldots,n$. Its squared target-jump sum is

$$\sum_{j=-n}^{n-1}|y_{j+1}-y_j|^2=8n+2/n\longrightarrow\infty.\tag{8}$$

Nevertheless its consecutive-edge infinitesimal mass flow is only $1/(8n^2)$, whereas the same-parity flow is $(1-1/(4n^2))/4$. The interface budget of this diagram is exactly

$$\sum_{i<j}g_{ij}|y_i-y_j|^2
=1+\frac1{4n^2}+(2n-1)\left(\frac1{2n}-\frac1{8n^3}\right)<3.\tag{9}$$

Thus the many-cell geometry permits long paths, but allocates little conductance to their long jumps. A bound using **actual flow weights** could still be uniform. Replacing the flow by its total endpoint weight times the worst path cost loses this distinction. Conversely, (9) alone does not establish such a bound. Bounded multiplication of the source density changes conductances by bounded factors and cannot remove the $n^2$ contrast in (7).

Both $\nabla U_n$ and $\nabla U_n(\cdot,\cdot+t)$ are the unique optimal maps to their own laws for every admissible source, by the finite-maximum Fenchel argument. The exact experiment computes their laws, all cell intersections, and an exact rational optimal target cost. It includes increasing-degree smooth densities with the same bounds $1/8,3/8$. It is a falsification test of this candidate amplifier, not a proof of a new modulus; the all-$n$ statements (6)–(9) are proved independently above.

### 2.3 Construct a special gluing before estimating it

For finite targets let $P_i,Q_j$ be the actual cells, $r_{ij}=\rho(P_i\cap Q_j)$, and let $\pi=(\pi_{ij})$ be an optimal target coupling. Define $a_{ij}=\min(r_{ij},\pi_{ij})$. On $P_i\cap Q_j$, put the diagonal source coupling of mass $a_{ij}$, using the submeasure $(a_{ij}/r_{ij})\rho|_{P_i\cap Q_j}$ when $r_{ij}>0$. Subtract these submeasures from the source restrictions on each $P_i$ and each $Q_j$, obtaining nonnegative residuals $\alpha_i,\beta_j$. Let $p_{ij}=\pi_{ij}-a_{ij}$, whose row and column sums are their masses. For each positive $p_{ij}$, couple

$$\frac{p_{ij}}{|\alpha_i|}\alpha_i
\quad\text{to}\quad
\frac{p_{ij}}{|\beta_j|}\beta_j$$

using the product of the normalized residual laws, or a quadratic optimal coupling of those residual laws. Summing produces an actual coupling $\Gamma$ of two copies of $\rho$, with $(T_\mu(X),T_\nu(X'))\sim\pi$. Zero residual rows/columns have no positive entries and are omitted. In particular

$$\mathbb E_\Gamma|X-X'|^2
\le\operatorname{diam}(K)^2\left(1-\sum_{ij}a_{ij}\right)
=\operatorname{diam}(K)^2d_{TV}(r,\pi).\tag{10}$$

One can minimize the source displacement over all such gluings. Existence follows by compactness of couplings of $\rho$ with itself. The constraints on cell products pass to the limit because their boundaries have zero mass under either fixed marginal. Formula (10) constructs a feasible competitor, so no existence or marginal constraint is assumed away. This differs from using independent complete conditional cell laws for every target pair.

The remaining problem is to estimate the *weighted geometric* discrepancy between $r$ and a suitable optimal $\pi$. The common-source coupling $r$ is generally not optimal. Its unweighted TV discrepancy need not decrease when all target sites coalesce.

### 2.4 An actual optimal-pair test rejects an unscaled source-displacement shortcut

The tempting bound $\|X-X'\|_2\lesssim D$ for some optimal-target gluing is false uniformly on fixed $K,Y$. This is not the old nonoptimal sign-swap example. Set $p=(1,0)$, $q=(3/5,4/5)$, and for $0<\lambda\le1$ let

$$\mu_\lambda=\tfrac12(\delta_{-\lambda p}+\delta_{\lambda p}),\quad
\nu_\lambda=\tfrac12(\delta_{-\lambda q}+\delta_{\lambda q}),\quad \rho=\tfrac14 1_K dx.$$

The maps are $\lambda p\operatorname{sign}(p\cdot x)$ and $\lambda q\operatorname{sign}(q\cdot x)$. Since $p\cdot q>0$, the unique optimal target coupling matches corresponding signs, and

$$w^2=\tfrac45\lambda^2,\qquad D^2=\tfrac{31}{20}\lambda^2.\tag{11}$$

For the second identity, the source sign correlation is $3/8$; it follows by integrating the two triangles of disagreement in the square. Every admissible source gluing must couple $P_+=\{x>0\}$ to $Q_+=\{3x+4y>0\}$, and the negative halves correspondingly. Their conditional centroids are

$$c_P=(1/2,0),\qquad c_Q=(1/4,13/32).$$

Jensen's inequality on each half gives, for **every** such gluing,

$$\mathbb E|X-X'|^2\ge|c_P-c_Q|^2=233/1024.\tag{12}$$

Thus (10) cannot generally be replaced by $O(D^2)$. Even the proposed improved repaired correlation gap $G\lesssim wD$ fails: the unique target repair from the first map to the second has

$$G=\lambda\left(\mathbb E|q\cdot X|-\mathbb E[(q\cdot X)\operatorname{sign}X_1]\right)
=7\lambda/40,$$

whereas $wD=O(\lambda^2)$. All maps and costs here are optimal at their own marginals. Q is completely consistent with (11): $D^3/w=O(\lambda^2)$. A future route must retain target-scale information rather than demand this unscaled gluing estimate. No claim that every suitably scaled or jump-weighted repair estimate fails is made.

## 3. Constructive route B: entropic bias with the correct dual shifts

Use the objective $\int |x-y|^2/2\,d\gamma+\varepsilon\operatorname{KL}(\gamma\mid\rho\otimes\mu)$, with both marginals constrained. Its barycentric map is $T_\varepsilon(x)=\mathbb E[Y\mid X=x]=\nabla u_\varepsilon(x)$. For compact supports, DNWP supplies

$$\|T^\mu_\varepsilon-T^\nu_\varepsilon\|_2
\le(1+2RL/\varepsilon)w.\tag{13}$$

Indeed the forward/backward conditional covariance operator bounds are $L^2,R^2$. Equation (13) is target-uniform. To derive Q it would suffice to prove the **actual squared bias**

$$B_\varepsilon(\rho,\mu):=\|T_\varepsilon-T_0\|_2^2\le B(K,Y,c,C)\varepsilon
\quad(0<\varepsilon\le1)\tag{UB}$$

uniformly in both the source class and *every* finite target. Then squared triangle inequality with (13), $\varepsilon=w^{2/3}$ for $w\le1$, and the trivial map bound for $w>1$, would give Q. The measurable-source and general-target limits are addressed below; UB itself is not proved.

### 3.1 A genuinely uniform estimate, for conditional variance

The Gibbs Hessian identity, with this half-squared-cost convention, is

$$\varepsilon D^2u_\varepsilon(x)=\operatorname{Cov}(Y\mid X=x).$$

The globally defined entropic potential is smooth with gradient in $\operatorname{conv}Y\subset B_L$. For finite targets this follows by differentiating the finite exponential sum. For arbitrary compact targets, the two Schrödinger equations give bounded oscillation of the dual potentials on the supports; after normalization the exponential integrals are finite, and bounded $Y$ allows all differentiations under the integral. The same identity follows. Applying the coordinate-slice budget gives

$$V_\varepsilon:=\int\mathbb E[|Y-T_\varepsilon(X)|^2\mid X=x]\,d\rho(x)
=\varepsilon\int_K f\Delta u_\varepsilon dx
\le2CLP_K\varepsilon.\tag{14}$$

No source derivatives, density lower bound, atom count, or mass lower bound is used. This is a direct technical consequence of the known Hessian identity and convex BV budget. It also gives $W_2^2((T_\varepsilon)_\#\rho,\mu)\le V_\varepsilon$, but that statement concerns a different target.

The exact orthogonal decomposition is

$$\iint |y-T_0(x)|^2\,d\gamma_\varepsilon(x,y)=B_\varepsilon+V_\varepsilon.\tag{15}$$

An upper bound on the second summand is not an upper bound on the first.

### 3.2 Why convexity, correct marginals, and small variance alone do not imply UB

There is an explicit smooth-source test for this distinction. Let $0<b\le a/2<1/4$, with uniform source on the square. Define

$$S=\nabla\max(-x,a,x),\qquad
T=\nabla\max(-x,a-b/2+b|y|,x).$$

The law of $S$ has central mass $a$ at zero and outer masses $(1-a)/2$ at $\pm e_1$. The law of $T$, denoted $\mu$, splits that central mass equally between $\pm be_2$, retaining the outer masses. Construct a feasible plan with target $\mu$: over the central strip of $S$, independently choose $\pm be_2$ with equal probabilities; outside it choose the outer value of $S$. Its barycentric map is exactly the convex gradient $S$; its integrated conditional variance is

$$V=ab^2.$$

Nevertheless its squared barycentric bias relative to the true optimal map $T$ is

$$\|S-T\|_2^2=b/4+ab^2.\tag{16}$$

To verify (16), the new middle half-width is $a+b(|y|-1/2)$. Averaging its absolute difference from $a$ gives $b/4$; the vertical component contributes $ab^2$. At $b=a/2$, the ratio of (16) to $V$ diverges like $1/(2a^2)$. The source is uniform and both deterministic maps are actual optimal maps; the feasible plan has correct marginals and a convex-gradient barycenter. It is **not** the entropic optimizer. This example rules out deducing UB solely from those properties and (14). The Gibbs optimality condition is an essential unpaid part of the bias problem. Its target $W_2^2=ab^2$, by matching and vertical projection, so this is another technical variant of cube-root sharpness, not a refutation of Q.

### 3.3 The exact counting-measure conversion

Write $\mu=\sum_i m_i\delta_{y_i}$, all $m_i>0$. DNWP's relative-reference dual gives

$$p_i(x)=\frac{m_i\exp((x\cdot y_i-\psi_{\varepsilon,i})/\varepsilon)}
{\sum_jm_j\exp((x\cdot y_j-\psi_{\varepsilon,j})/\varepsilon)}.
$$

Put

$$q_{\varepsilon,i}=\psi_{\varepsilon,i}-\varepsilon\log m_i.
\tag{17}$$

Then $p_i=\exp((x\cdot y_i-q_{\varepsilon,i})/\varepsilon)/\sum_j\exp((x\cdot y_j-q_{\varepsilon,j})/\varepsilon)$. These $q_\varepsilon$ are the counting-measure dual coordinates. The two entropy objectives differ by the fixed marginal constant $H(\mu)$, so the coupling and barycentric map are exactly unchanged. At zero regularization $q_0=\psi_0$, modulo constants.

[Delalande's published paper](https://proceedings.mlr.press/v151/delalande22a/delalande22a.pdf), §2.1, explicitly uses counting measure. Its Corollary 2.2 (the published numbering) proves $\|q_\varepsilon-q_0\|_\infty=O_{\rho,\mu}(\varepsilon^{1+\alpha'})$ for $0<\alpha'<\alpha$, under a fixed Hölder source and fixed positive finite configuration, after its normalization. The displayed constants depend on $N,m_{\min}$, separation, angular geometry, and source Hölder data. Altschuler–Niles-Weed–Stromme §2.2 makes the same counting-measure conversion before its $o(\varepsilon)$ dual asymptotic.

Thus the corresponding relative-reference statement is

$$\inf_k\max_i|\psi_{\varepsilon,i}-\psi_{0,i}-\varepsilon\log m_i-k|
=o_{\rho,\mu}(\varepsilon),\tag{18}$$

not the same assertion with the logarithmic term omitted. DNWP v1's equation (22) cannot be used literally with its earlier relative-reference definition. Its Proposition 4.1 pairwise bound is still a useful upper bound when its actual dual difference is retained. Rewriting the proof using $q$ supplies the configuration-dependent bias estimate needed for its stated stability conclusion. This is a convention repair in using this external interface, not a rejection of BT or a claim about an unread published correction.

### 3.4 Exact two-atom diagnostic and a true uniform bias theorem

For the uniform square and target $m\delta_{-e_1}+(1-m)\delta_{e_1}$, $0<m<1$, let $b=2m-1$. The optimal map is $\operatorname{sign}(x-b)e_1$. The entropic map is

$$T_\varepsilon(x,y)=\tanh((x-b_\varepsilon)/\varepsilon)e_1,$$

where the marginal constraint gives the exact threshold

$$b_\varepsilon=b+\frac\varepsilon2\log\frac{1-e^{-4m/\varepsilon}}{1-e^{-4(1-m)/\varepsilon}}.\tag{19}$$

Consequently

$$ (\psi_{\varepsilon,+}-\psi_{\varepsilon,-})
-(\psi_{0,+}-\psi_{0,-})
=\varepsilon\log\frac{1-m}{m}+2(b_\varepsilon-b).$$

For each fixed $m$, $b_\varepsilon-b=o(\varepsilon)$, verifying the nonconstant logarithmic shift directly. In the same order of limits,

$$\lim_{\varepsilon\downarrow0}\frac{B_\varepsilon}{\varepsilon}
=2\log2-1,\qquad
\lim_{\varepsilon\downarrow0}\frac{V_\varepsilon}{\varepsilon}=1.\tag{20}$$

For the first limit, substitute $z=(x-b)/\varepsilon$ and use
$\int_0^\infty(1-\tanh z)^2dz=2\log2-1$. The second is the integral of $\operatorname{sech}^2z$, with the marginal density factor $1/2$. Exponentially small threshold corrections in (19) do not change these limits for fixed $m$.

DNWP's displayed facet/log-ratio expression in this example is $-\log(m(1-m))$, which diverges as $m\downarrow0$. The true coefficient in (20) does not diverge. That expression is an upper-bound expression, not an equality identifying the true bias. Its printed limit direction and equality symbol are not used as a theorem here.

There is also a **nonasymptotic, mass-uniform** bound, which does not require source smoothness. For any two distinct sites $y_-,y_+$, let $s=|y_+-y_-|$, $n=(y_+-y_-)/s$, and
$A_n=|\operatorname{proj}_{n^\perp}K|_{d-1}$. For every $f\le C$, every pair of masses, and every $\varepsilon>0$,

$$\boxed{B_\varepsilon\le2CA_n s\,\varepsilon\log2.}\tag{21}$$

**Proof.** The projected source coordinate $r=n\cdot x$ has a density $g(r)\le CA_n$. The unregularized map uses a threshold $b$; the entropic probability of the plus site is $p(r)=\sigma(s(r-b_\varepsilon)/\varepsilon)$, with $b_\varepsilon$ determined by the same target mass. Let

$$e_- =\int_{r<b}p(r)g(r)dr,\qquad
e_+=\int_{r>b}(1-p(r))g(r)dr.$$

Equality of the plus marginal gives $e_-=e_+$. If $b_\varepsilon\ge b$, bound $e_-$ by $CA_n\int_{-\infty}^b\sigma(s(r-b)/\varepsilon)dr=CA_n\varepsilon\log2/s$. If $b_\varepsilon\le b$, bound $e_+$ by the equal right-tail integral. The total conditional squared error against the optimal map is $s^2(e_-+e_+)$; Jensen bounds $B_\varepsilon$ by this quantity. This proves (21). Zero mass or coinciding sites gives zero bias by merging. No density derivative or minimum mass appears. Existence and uniqueness of the threshold follows from the strictly monotone continuous logistic integral, with limits zero and one. ∎

The key operation is balancing the two error flows using the *exact target marginal*. With many atoms, the errors can circulate through multiple cells. An extension must preserve the squared jump costs in those flows, not pay one full target diameter for each intermediate label.

### 3.5 A uniform limiting coefficient for finite configurations, with the quantifiers in the correct order

For each fixed smooth positive $f$ and each fixed finite distinct positive target, (18) and the pairwise softmax bound in counting coordinates imply

$$\limsup_{\varepsilon\downarrow0}\frac{B_\varepsilon}{\varepsilon}
\le2\log2\sum_{i<j}|y_i-y_j|\int_{F_{ij}}f\,dS
\le4\log2\,CLP_K.\tag{22}$$

Here is a direct proof of the first inequality. On the unregularized cell $P_i$, set
$d_{ij}(x)=x\cdot(y_i-y_j)-q_{0,i}+q_{0,j}\ge0$, and
$\delta_\varepsilon=\inf_k\|q_\varepsilon-q_0-k\|_\infty$. Then

$$p_j(x)\le e^{2\delta_\varepsilon/\varepsilon}
(1+e^{d_{ij}(x)/\varepsilon})^{-1}.$$

Jensen bounds pointwise bias by $\sum_jp_j|y_i-y_j|^2$. Coarea gives, for each ordered pair,

$$\int_{P_i}\frac{|y_i-y_j|^2f(x)}{1+e^{d_{ij}(x)/\varepsilon}}dx
=\varepsilon |y_i-y_j|\int_0^\infty\frac{H_{ij}(\varepsilon z)}{1+e^z}dz,$$

where $H_{ij}(t)$ is the density integral on the section $P_i\cap\{d_{ij}=t\}$. It is bounded by a fixed projected-volume bound times $C$. For continuous $f$, its limit as $t\downarrow0$ is the facet integral (zero for a lower-dimensional face). This follows by identifying parallel hyperplanes and dominated convergence off their boundary and competing tie sets; positive cells exclude coincident triple tie planes. Dominated convergence and $\int_0^\infty(1+e^z)^{-1}dz=\log2$ apply for this fixed finite collection. The prefactor tends to one by (18). Ordered pairs count each facet twice. Finally use (4).

Equation (22) proves

$$\sup_{\substack{f\text{ smooth},\ c\le f\le C\\\mu\text{ finite}}}
\limsup_{\varepsilon\downarrow0}B_\varepsilon/\varepsilon
\le4\log2\,CLP_K.$$

It does **not** prove $\limsup_{\varepsilon\downarrow0}\sup_{f,\mu}B_\varepsilon/\varepsilon<\infty$. The onset and coarea convergence remain configuration-dependent. Neither source approximation nor a growing finite net may be interchanged with this limit. The bound is a technical use of known dual asymptotics and BV, not the desired new bridge.

### 3.6 Growing near-coincident clusters refute a uniform individual-dual correction bound

Even with uniform source, the sufficient shortcut
$\operatorname{osc}(q_\varepsilon-q_0)\le A\varepsilon$ for all finite targets is false. Fix $M\ge2$, $\varepsilon>0$, distinct numbers $s_i\in[-1,1]$, and target

$$\mu_{M,\delta}=\tfrac12\delta_{e_1}+\frac1{2M}\sum_{i=1}^M\delta_{\delta s_i e_2},\qquad\delta>0.$$

Use counting **intercepts** $c_i=-q_i$, normalizing the external intercept to zero. The entropy marginal constraints give, for cluster indices $i,j$ of equal mass,

$$|c_i^\varepsilon-c_j^\varepsilon|\le R|y_i-y_j|.$$

Indeed the pointwise conditional ratio is $\exp((x\cdot(y_i-y_j)+c_i-c_j)/\varepsilon)$; if $c_i-c_j>R|y_i-y_j|$, its integral would make the $i$-mass strictly larger, and conversely. Thus as $\delta\downarrow0$ the cluster intercepts share a common limiting value. More explicitly, write
$B=\varepsilon\log\sum_i e^{c_i^\varepsilon/\varepsilon}$. The external probability differs uniformly, for bounded $B$, from $\sigma((x_1-B)/\varepsilon)$ by a quantity tending to zero. Its marginal is $1/2$; elementary upper and lower logistic comparisons first bound $B$, and then force $B\to0$ by symmetry and strict monotonicity. It follows that

$$c_i^\varepsilon\longrightarrow-\varepsilon\log M\qquad(1\le i\le M).$$

For the unregularized intercepts, positive cluster cells imply $|c_i^0-c_j^0|\le R|y_i-y_j|$, by comparing strictly active points. After the same normalization they are bounded: existence of a positive external cell gives an upper bound for each cluster intercept, and positive cluster cells give lower bounds. In the limit they all have one value $c^0$. The collapsed external mass is $1/2$, so the limiting potential $\max(x_1,c^0)$ must have threshold zero. Hence $c_i^0\to0$. Consequently

$$\lim_{\delta\downarrow0}\frac{\operatorname{osc}(c^\varepsilon-c^0)}{\varepsilon}=\log M.\tag{23}$$

All sites are distinct for $\delta>0$, all masses are positive, $K$ and density are fixed, and targets remain in a fixed square. Choosing, for example, $\varepsilon_M=M^{-2}$, and then a sufficiently small positive $\delta_M$, gives divergence at a regularization scale tending to zero. This is an analytic growing-atom example, not a floating simulation. The quantifier order in that choice is essential.

There is no bias counterexample hidden here. For fixed $M,\varepsilon$, as $\delta\downarrow0$, the entropic barycenter converges uniformly to the two-atom barycenter for $\tfrac12(\delta_0+\delta_{e_1})$. The unregularized maps converge strongly by the compactness/uniqueness argument in §1.2. Thus their bias converges to that two-atom bias, bounded by (21). Large corrections in individual label coordinates compensate multiplicity inside a tiny cluster. A viable proof of UB must measure a quantity unchanged by such splitting, or estimate the resulting map directly.

### 3.7 What a valid uniform estimate would allow one to pass to limits

If UB were proved for smooth sources and finite targets with the asserted single constant, the measurable-source limit at fixed finite target and fixed $\varepsilon>0$ would be legitimate. The finite entropic dual objective is strictly convex modulo constants, and its normalized minimizers stay in a compact set: marginal ratios give bounds depending on the fixed positive masses, $R,L,\varepsilon$. Its integrals vary continuously under $L^1$ changes of $f$. Every limiting minimizer is the unique minimizer for the limiting source, so the finite softmax maps converge uniformly. The unregularized maps converge strongly as in §1.2. This passes UB to measurable $f$, without preserving source derivatives.

Alternatively one can combine UB and (13) before taking any target limit, obtaining a finite-target Q constant independent of $N$. Then use finite target nets and the qualitative convex-potential compactness argument of §1.2 to pass Q to arbitrary compactly supported targets. This avoids needing an entropic target approximation theorem. These are justified limiting operations **conditional on an actually uniform UB**; they cannot be applied to (22), whose quantifiers are weaker.

## 4. Adversarial assessment and exact remaining interfaces

The growing zigzag diagram tests real cells and real target laws. Its long paths disprove worst-path diameter control, while its conductance contrast prevents that observation alone from disproving weighted reassignment control. Exact polygon integration and exact minimum-cost flow were run for 11 target pairs with up to 33 atoms; four use increasing-degree polynomial densities $f=(1+\tfrac12 yT_{2n-1}(x))/4$, smooth with uniform bounds $1/8,3/8$. The chosen perturbations are $t=1/(100n^2)$. Every consecutive path edge has positive actual reassignment mass. All exact $D^6/W_2^2$ values are finite and small in these tests; this is not a uniform theorem. The all-$n$ formulas, rather than those finite values, justify the path obstruction.

The growing-cluster example retains distinct sites and exactly prescribed positive masses, and proves a nonuniform dual correction. It explicitly compares the true bias in its coalescing limit, so it cannot be mistaken for an entropic bias counterexample. The two-atom and split-center computations separately expose logarithmic upper-bound artifacts and the difference between conditional variance and bias. All examples live on a single fixed convex square with strictly positive bounded density; higher-dimensional versions follow by adjoining independent uniform cube coordinates.

Several additional amplification ideas were screened. Independently combining localized gadgets with a *uniform normalized* cube-root estimate cannot amplify their ratio: if a partition has weights $p_i$, normalized squared errors $E_i$, and normalized target costs $W_i$ with $E_i^3\le A W_i$, Jensen gives $(\sum p_iE_i)^3\le A\sum p_iW_i$. This statement does not assume that arbitrary gadgets can be realized as one optimal map, nor that the mixture coupling is target-optimal; it only rules out that particular upper-cost/lower-error strategy for proving a counterexample. Thin-domain rescaling can change the local constant, and would need its own geometry analysis. Adding a uniform density floor to disconnected-support examples changes both optimal partitions and target transport; no preservation of their lower bounds has been proved.

The unpaid interfaces are now precise:

1. **Geometric route:** control actual weighted reassignment or a specially optimized target gluing uniformly through long paths, small slopes and tiny cells. Equations (4)–(10) construct and bound legitimate objects, but do not relate their remaining weighted defect to $w$ with the needed power. The unscaled $S\lesssim D$ and $G\lesssim wD$ shortcuts are actually false by (11)–(12).
2. **Entropic route:** turn exact marginal balance and Gibbs structure into UB for arbitrarily many atoms, using a quantity unchanged by splitting an atom into a small cluster. Equation (14) bounds only conditional variance; (22) is only a fixed-configuration asymptotic; (23) blocks the most direct uniform individual-dual correction bound. None is substituted for UB.

The previously rejected upgrades remain rejected: compensated Moreau error is genuinely quadratic, not cubically small in general; generic repaired-plan conditioning cannot be strengthened using the old sign-swap feasible plan as though it were a pair of optimal maps; the false weighted moment estimate cannot be recovered from its unchanged scalar Laplacian. No different sharp modulus for Q has been established.

## 5. Bounded primary-source comparison and evidence scope

Fresh current arXiv metadata confirms LM v3, Ruan v1, Wang–Wang v1, DNWP v1, BK v2, Ford v1, and the inspected Altschuler and Mulcahy–Pal v1 versions. The HAL landing response cites `hal-05616391v1`. Requests, response bytes and hashes are retained. Existing primary PDF/text pairs are reused by hash rather than recopied. The full direct BT manuscript is the only family374 manuscript in the complete pinned inventory; broader transport titles are different problems, not evidence of a missing density extension. This is a bounded search conclusion, not exhaustive semantic novelty certification.

- [Letrouit–Mérigot v3](https://arxiv.org/abs/2411.04908v3), Theorem 2.1 and its four-step proof, supplies the comparable-density variance coercivity through tilted measures and Brascamp–Lieb. Proposition 2.2 supplies gradient interpolation. Neither asserts the false linear-potential estimate; no inverse-moment bound is inferred from it.
- [Ruan v1](https://arxiv.org/abs/2610.07577v1), Definition 3, §11 and Theorem 8, constructs the target-repaired plan and bounds its objective gap. At bounded source density the resulting map exponent is $1/4$ in $W_1$. It is not $1/3$ in $W_2$. Its repair is compared with the constructed gluing in §2.3, not identified with it.
- [Wang–Wang v1](https://arxiv.org/abs/2610.09640v1), Lemmas 6–8 and the proof of Theorem 1, gives the compensated nonnegative Moreau error and the correlation-gap gluing. Using uniform measure on $K$ as BV reference covers our measurable density class with derivative-free constants and yields the already available quarter-power bound.
- [Mérigot HAL v1](https://hal.science/hal-05616391v1), Theorem 3.4 and §4, converts an arbitrary feasible-plan gap into squared map error of order the square root of that gap. Its semi-discrete entropic application uses a configurationwise quadratic cost-gap asymptotic. A finite limiting cost-gap coefficient is not a uniform estimate over targets.
- [Ford v1](https://arxiv.org/abs/2609.35574v1), Proposition 5.2, constructs separated rectangular source pieces with density zero outside their union. The inspected explicit construction fails the positive lower bound on all of $K$. No admissible counterexample to Q follows by calling its convex container the source support.
- [Bansil–Kitagawa v2](https://arxiv.org/abs/2002.02022v2), Theorem 1.3 and §2's exchange-digraph proof, already supplies the acyclic reassignment operation with atom dependence. The source's stated general bound and I33's sharper elementary quadratic specialization are distinguished. The analytic obstacle is removing that dependence while retaining geometry and costs.
- [DNWP v1](https://arxiv.org/abs/2404.02855v1), equations (7)–(12), Theorem 3.1 with its conditional-KL proof, Proposition 4.1 and its full appendix, give exactly the entropic conventions, target-uniform stability, and configuration-dependent bias interface used here. Delalande's published §2.1 and Corollary 2.2, and [Altschuler–Niles-Weed–Stromme v1](https://arxiv.org/abs/2106.11862v1), §2.2 and Theorem 1.3, identify the counting-measure shift. Equations (17)–(22) are a technical repair/application of those operations, not an independent general bias theorem.
- [Mulcahy–Pal v1](https://arxiv.org/abs/2609.22595v1), Assumption 1 and Main Theorem 1, was checked after a fresh query. Its source and target have full-support $C^3$ uniformly strongly log-concave densities; the Brenier potential has bounded higher derivatives. Its score expansion is a fixed-data $o(\varepsilon)$ statement. These hypotheses and its remainder do not supply UB for bounded measurable sources and arbitrary atomic targets. This is a hypothesis screen, not a claim to have audited that paper's entire proof.

The old failed publisher downloads remain frozen as historical failures, including the HTML challenge and HTTP 403; the successful BK NSF copy remains preserved. This round does not claim that those failed endpoints were successfully read, or that the published DNWP version was compared. The first exploratory web result was visible but not serialized; the subsequent search is serialized with its exact request and response. Its noisy search hits are not mathematical dependencies. A missing optional SymPy package caused the first diagnostics invocation to fail before doing work; the final diagnostic uses only Python's standard library and exact rational arithmetic. No package installation or other-project write was used.

## 6. Reproduction, preservation, and handoff

From the project root run:

```bash
python frontier/experiments/i34_target_uniform_brenier/diagnostics.py
python frontier/experiments/i34_target_uniform_brenier/verify.py
```

The first checks the I33 formulas, exact half-plane centroids and costs, 197 nonzero facet coefficients across the growing diagrams, 11 exact growing-diagram optimal-target comparisons, and 12 exact split-center optimal-target comparisons. Its arithmetic imports the prior rational polygon/min-cost-flow functions with `runpy` under a non-main name, so the prior script does not run its writer and no bytecode cache is created there. The second checks the artifact seal, frozen inputs, unchanged prior artifacts, selected pinned Git/SHA/URL identities, the entire reused corpus and complete tree, exact read-passage hashes, and fresh and reused primary response/extraction hashes. Shared-ledger drift is reported separately from frozen integrity; non-ledger mathematical dependency drift is an error.

The seal excludes its own bytes and generated verification/drift outputs. The report, full task brief, full original I32/I33 briefs, prior reports and objections, source contracts, scripts and exact diagnostics are retained. The read log records opened line ranges; it does not equate a corpus text search or hashing with reading every proof. Script verification is evidence of reproducibility and preservation, not a certificate of all analytic arguments.

The handoff is an audited I33 premise set and a more developed many-cell/bias gap. Q still needs one of the unpaid interfaces above, or an actual admissible sequence with an optimal-map lower bound and a target-cost upper bound whose cube-root ratio diverges. No such sequence, target-uniform theorem, count change, or priority claim is supplied.
