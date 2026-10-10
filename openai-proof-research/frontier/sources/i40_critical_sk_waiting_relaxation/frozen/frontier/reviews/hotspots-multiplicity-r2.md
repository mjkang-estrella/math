# Hot spots multiplicity review, round 2

**Parent status: demoted as a candidate for the requested significant novel advance.** The [round-3 novelty review](hotspots-polygon-novelty-r3.md) found no proof gap but identified the smooth boundary mechanism and polarization in existing literature. Only the short vertex extension remains potentially new; priority is unconfirmed. The [separate adversarial proof review](hotspots-polygon-proof-r3.md) also accepted the mathematics, with explicit analytic clarifications. The integrated technical record is [R003](../findings/R003-polygon-eigenline-selection.md). The parent reran the exact corner-parity checks successfully; these do not validate the full theorem. The earlier separation lemma is classical (Bérard–Helffer 2021, Lemma 4.3). No high-tier MathDB ranking or literature priority is claimed.

Date: 2026-10-08. Scope: research on the repeated-first-positive-eigenvalue gap in `frontier/scouts/analysis.md`, not an audit of the accepted corpus. Corpus revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## Result and disposition

**The general Lipschitz eigenline-selection problem is not closed here. There is, however, a complete closure for every bounded simply connected polygon, with no convexity, symmetry, or simplicity assumption.** The new step is a two-edge corner argument proving surjectivity of the traceless shape-derivative map. It handles reentrant vertices, including the potentially troublesome angle $3\pi/2$.

More precisely:

1. For every bounded simply connected planar Lipschitz domain, the first positive Neumann eigenspace has dimension at most two. Section 2 proves this without boundary derivatives, rather than extrapolating a smooth multiplicity theorem.
2. For every bounded simply connected polygon $P$, every nonzero $u\in E(P)$ is a $C^\infty_{\rm loc}(P)$ limit of first-positive eigenfunctions on bounded simply connected smooth domains. These approximating first-positive eigenvalues can be taken simple. Section 5 proves this, including selection of the **lower** split branch.
3. Consequently, under the accepted corpus theorem 369 and the scout's separation argument, **every** first-positive eigenfunction on **every** bounded simply connected polygon satisfies strict boundary-only global extrema. Section 6 supplies the conclusion and checks the bridge used to obtain it.

This is a genuine additional argument beyond generic simplicity or spectral convergence. It is new to this project; literature priority for the shape-transversality/corner argument has **not** been established. It advances the named-tier MathDB hot-spots target, not a demonstrated landmark/celebrated-tier target. Do not advertise a solution for all Lipschitz domains.

All writes from this review are confined to this file and `frontier/{sources,experiments}/hotspots_multiplicity_r2/`. No shared-file edits, staging, commits, or nested agents were used.

## 1. Exact source contracts

The following actual texts were read. Download URLs, byte counts, and SHA-256 hashes are recorded in [`../sources/hotspots_multiplicity_r2/manifest.json`](../sources/hotspots_multiplicity_r2/manifest.json).

**Accepted corpus input.** Family 369, `Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/build/sections/01-introduction.tex`, `thm:main`: bounded, nonempty, simply connected planar domain with $C^\infty$ boundary; every nonzero eigenfunction for the first positive Neumann eigenvalue has nonvanishing interior gradient. Multiplicity is allowed. [Pinned source](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/build/sections/01-introduction.tex).

The same manuscript's `02-preliminaries.tex` gives `lem:gap`, `lem:nodal`, `lem:boundary-weight`, and `prop:multiplicity`, under its standing **smooth** hypotheses. The last proof uses positive boundary weights and a first-harmonic sign test. Section 2 below replaces the smooth normal-derivative construction by a finite-dimensional positive-measure construction. This is a checked extension of that argument, not a claim that its original hypotheses already cover Lipschitz domains. [Pinned source](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/build/sections/02-preliminaries.tex).

**Boundary continuity.** Robin Nittka, *Regularity of solutions of linear second order elliptic and parabolic boundary value problems on Lipschitz domains*, JDE 251 (2011), 860–880, Theorem 3.14(ii), in [arXiv:0906.5285](https://arxiv.org/pdf/0906.5285). In dimension two, take $q=N/2=1$, $\varepsilon=1$, $f_0=\mu u\in L^2$, zero divergence data and zero Neumann data. It gives $u\in C^{0,\gamma}(\overline\Omega)$. No boundary differentiability of $u$ is inferred.

**Topology-preserving smooth approximation.** John M. Ball and Arghir Zarnescu, *Partial regularity and smooth topology-preserving approximations of rough domains*, [arXiv:1312.5156](https://arxiv.org/pdf/1312.5156), Theorem 5.1 and Remark 5.3. For bounded Lipschitz $D$, these provide smooth inner domains $D_\varepsilon$, homeomorphic closures, and uniformly bi-Lipschitz maps $F_\varepsilon:\overline D\to\overline {D_\varepsilon}$. The maps equal the identity outside a shrinking boundary collar. Section 5 derives precisely the needed spectral convergence from this contract. This avoids depending on an unchecked Verchota theorem number.

**Corner expansion.** Chris Judge and Sugata Mondal, *Euclidean triangles have no hot spots*, Ann. Math. 191 (2020), 167–211, Section 4, equations (5), (6), and (10), pp. 178–181: separation-of-variables expansion for a Helmholtz solution on a sector, with homogeneous Neumann conditions on its two straight sides; no condition is imposed on the outer circular arc. We use the expansion and its termwise radial derivative, which apply to reentrant sectors as well. Section 5, Corollary 5.4, also explicitly states multiplicity at most two for simply connected polygons. We do **not** rely on Lemma 3.4 or the hot-spots proof affected by the later erratum. [Primary journal PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v191-n1-p03-s.pdf).

Other standard inputs used explicitly below: compactness of $H^1(D)\hookrightarrow L^2(D)$ on bounded Lipschitz domains, Sobolev traces, interior elliptic regularity/analyticity, the Jordan curve theorem, and elementary finite-dimensional convex separation. The perturbation and eigenline-selection claims are proved below rather than attributed to a generic-simplicity theorem.

## 2. Multiplicity at most two on all simply connected Lipschitz domains

Let $\Omega\subset\mathbb R^2$ be bounded, simply connected, and Lipschitz. Set $\mu=\mu_1^N(\Omega)>0$, $E=E(\Omega)$, and $\lambda_D=\lambda_1^D(\Omega)$. All functions are real unless explicitly complexified.

### 2.1 The strict Dirichlet gap does extend

The corpus's plane-wave proof of $\mu<\lambda_D$ uses only the variational definitions, compactness, and the zero Dirichlet trace, so it works verbatim on Lipschitz domains. For completeness, let $\phi\ge0$ be a Dirichlet ground state and let $e_k(x)=e^{ik\cdot x}$, $|k|^2=\lambda_D$. Subtract a multiple of $\phi$ to make $e_k$ mean zero. Its quadratic form at $\lambda_D$ vanishes because both diagonal terms and the cross term vanish. Thus $\mu\le\lambda_D$. If equality held, these mean-zero functions would all be Neumann minimizers. Distinct plane waves span an infinite-dimensional space, and subtraction of multiples of one fixed function cannot make that space finite-dimensional. This contradicts compact resolvent. Therefore $\mu<\lambda_D$.

### 2.2 Every nonzero trace changes sign

Nittka's theorem gives continuous traces on the Lipschitz Jordan curve $\partial\Omega$. The trace map on $E$ is injective: zero trace would put an eigenfunction in $H^1_0(\Omega)$, contradicting the gap.

If $u|_{\partial\Omega}\ge0$, then $u^-\in H^1_0(\Omega)$. Testing the weak eigenvalue equation by $u^-$ gives

\[
\int|\nabla u^-|^2=\mu\int|u^-|^2.
\]

The Dirichlet gap implies $u^-=0$. Since $u\ge0$ and $\int u=0$, we have $u=0$. Applying this to $-u$ proves that every nonzero boundary trace takes both signs.

### 2.3 A full-support positive boundary measure annihilating the entire eigenspace

This step replaces all smooth boundary-normal calculations.

Let $m=\dim E$ and choose a basis $u_1,\ldots,u_m$. Parametrize the boundary by a homeomorphism $\gamma:S^1\to\partial\Omega$, and put

\[
U(s)=(u_1(\gamma(s)),\ldots,u_m(\gamma(s))).
\]

The origin lies in the interior of the convex hull $C=\operatorname{conv}U(S^1)\subset\mathbb R^m$. Otherwise finite-dimensional separation gives a nonzero $a\in\mathbb R^m$ with $a\cdot U(s)\ge0$ for all $s$, contradicting Section 2.2.

Let $\sigma$ be normalized Lebesgue measure on $S^1$, and $b=\int U\,d\sigma$. Choose $0<\eta<1$ so small that $-\eta b/(1-\eta)\in C$. Write this point as a finite convex combination of points $U(s_j)$, with weights $\alpha_j$. Then

\[
d\nu=\eta\,d\sigma+(1-\eta)\sum_j\alpha_j\delta_{s_j}
\]

is a positive probability measure of full support and satisfies

\[
\int_{S^1}u(\gamma(s))\,d\nu(s)=0\qquad(u\in E).
\]

The atomic part causes no difficulty: all traces and trigonometric test functions are continuous, and full support ensures strictly positive integrals of nonnegative continuous functions that are positive somewhere.

### 2.4 Boundary signs and the dimension bound

The positive and negative sets of a nonzero $u\in E$ are connected. The restriction-to-a-nodal-component Rayleigh argument proving this is entirely interior and variational: if three sign components existed, a mean-zero combination of two restrictions would again minimize the Rayleigh quotient and would vanish on the omitted open component, contrary to analyticity.

Consequently the boundary trace cannot take strictly alternating signs at four cyclically ordered boundary points. Indeed connect the positive pair by a simple arc through the positive interior and the negative pair similarly. Continuity and the Lipschitz boundary permit the short interior end segments. The two arcs have alternating endpoints in a Jordan domain, so they must intersect, a contradiction.

Suppose $m\ge3$. The two equations

\[
\int h(\theta)\cos\theta\,d\nu=0,
\qquad
\int h(\theta)\sin\theta\,d\nu=0
\]

have a nonzero solution $h=u\circ\gamma$, $u\in E$. Also $\int h\,d\nu=0$. Cut the circle at a point where $h<0$, and let $a,b$ be the infimum and supremum of its positive angles in that cut interval. Then $a<b$, there are no positive values outside ([a,b]), and no negative values inside ((a,b)); otherwise there would be four alternating strict signs. The function

\[
F(\theta)=\cos(\theta-(a+b)/2)-\cos((b-a)/2)
\]

is positive inside ((a,b)) and negative outside ([a,b]). Therefore $Fh\ge0$ everywhere and $Fh>0$ somewhere. Full support gives $\int Fh\,d\nu>0$, whereas the three orthogonalities give zero. Contradiction.

**Conclusion:** $\dim E(\Omega)\le2$ for every bounded simply connected planar Lipschitz domain.

This proof uses no smooth traces of gradients, no boundary nodal expansion, and no assumption that multiplicity is upper semicontinuous under smoothing. In fact multiplicities can increase in limits, so the latter would be an invalid argument.

## 3. New polygon lemma: boundary cross-stress cannot vanish identically

### Statement P

Let $P$ be a bounded connected polygonal Lipschitz domain. Holes are allowed in this lemma. Let $h,k\in H^1(P)$ be nonzero real Neumann eigenfunctions with the same eigenvalue $\lambda>0$. Then it is impossible that

\[
(\partial_\tau h)(\partial_\tau k)=\lambda hk                 \tag{P}
\]

on the relative interior of every side.

Straight-angle vertices may be deleted. Thus all actual vertex angles lie in $(0,2\pi)\setminus\{\pi\}$. The functions are analytic across each open side by even reflection. At vertices we use sector expansions, not a smooth-gradient assumption.

### 3.1 The smooth-side calculation

Write $w=hk$ on a side. If $w\ne0$ and $w'=0$ at a point, set $a=h'/h$, $b=k'/k$ there. Equation (P) says $ab=\lambda>0$, whereas $w'=0$ says $a+b=0$. This would give $ab=-a^2\le0$. Therefore $w$ has no nonzero stationary value in the interior of a side.

On a smooth closed boundary this already rules out (P), by taking a nonzero extremum of $w$. On a polygon we must also eliminate a nonzero extremum at a vertex.

### 3.2 Convex corners

At a vertex of angle $\beta<\pi$, write $\nu=\pi/\beta>1$. The Neumann sector expansion gives

\[
 h(r,\theta)=A+O(r^{\min\{\nu,2\}}),
 \qquad \partial_rh=O(r^{\min\{\nu-1,1\}}),
\]

and the same for $k$, whose vertex value is $B$. Both side derivatives tend to zero. Passing to the limit in (P) gives $AB=0$.

### 3.3 Reentrant corners: average the two edges

Let $\pi<\beta<2\pi$, so $1/2<\nu=\pi/\beta<1$. Normalize the first coefficients in the Bessel expansions so that, on the two rays $\theta=0,\beta$,

\[
\begin{aligned}
h_\pm(r)&=A\pm a r^\nu+b r^{2\nu}
                  +O(r^{3\nu}+r^2),\\
k_\pm(r)&=B\pm c r^\nu+d r^{2\nu}
                  +O(r^{3\nu}+r^2).
\end{aligned}                                                   \tag{3.1}
\]

The differentiated expansions are

\[
\begin{aligned}
h_\pm'(r)&=\pm\nu a r^{\nu-1}+2\nu b r^{2\nu-1}
                  +O(r^{3\nu-1}+r),\\
k_\pm'(r)&=\pm\nu c r^{\nu-1}+2\nu d r^{2\nu-1}
                  +O(r^{3\nu-1}+r).
\end{aligned}                                                   \tag{3.2}
\]

These estimates include the radial $J_0$ term and the corrections to $J_\nu$. They follow directly from the convergent sector series, also after radial differentiation. One can choose the sector radius with $\sqrt\lambda R$ sufficiently small, expand the smooth data on its circular arc, and use $J_{n\nu}(\sqrt\lambda r)/J_{n\nu}(\sqrt\lambda R)=O((r/R)^{n\nu})$ on a smaller radius to bound the tails and their derivatives.

**Differentiated-tail lemma (review repair).** Choose $\sqrt\lambda R\le1$ and write the arc coefficients as $g_n\in\ell^2$. The normalized Bessel factors satisfy $|J_{n\nu}(\sqrt\lambda r)/J_{n\nu}(\sqrt\lambda R)|\le C(r/R)^{n\nu}$ and, for $n>0$, a radial derivative bound $C(n\nu+1)r^{-1}(r/R)^{n\nu}$. The zeroth-mode derivative is $O(r)$. Cauchy–Schwarz gives uniform tail bounds $O(r^{N\nu})$ and $O(r^{N\nu-1})$ for modes $n\ge N$, including both boundary rays. Thus $N=3$ justifies (3.1)–(3.2). The normalized power-series proof and exclusion of irregular finite-energy branches are in [proof review §3.1](hotspots-polygon-proof-r3.md). In the average below, the displayed $bd$ term is not the full coefficient at order $r^{4\nu-2}$: first/third-mode products may also occur at that order, but are included in $o(1)$ because $4\nu-2>0$.

The product of tangential derivatives is independent of whether a side is parametrized toward or away from the vertex, so (P) applies to $h'_\pm k'_\pm$. Its right-hand side is bounded. Multiply either identity by $r^{2-2\nu}$ and let $r\downarrow0$:

\[
\nu^2ac=0.
\]

Thus $ac=0$. Now average the two identities. The mixed terms of order $r^{3\nu-2}$ have opposite signs and cancel. Equations (3.2) give

\[
\frac{h'_+k'_++h'_-k'_-}{2}
 =\nu^2ac r^{2\nu-2}+4\nu^2bd r^{4\nu-2}+o(1)\longrightarrow0,
\]

since $ac=0$ and $4\nu-2>0$. All products involving the remainders tend to zero: the worst additional exponents are $4\nu-2$ and $\nu$, both positive. Averaging the right-hand sides gives the limit $\lambda AB$. Hence again $AB=0$.

**Why the averaging is convenient:** at angle $3\pi/2$, $\nu=2/3$, a first-mode/second-mode derivative product has exponent $3\nu-2=0$. One cannot discard this finite term on a single side. Its sign reverses on the other side, so the average removes it exactly. Equivalently, adding the two single-edge limit identities gives the same conclusion; averaging is not indispensable. For still larger reentrant angles the term would diverge, but the same cancellation works.

An equivalent structural check: averaging the two rays kills all cosine-mode products with odd $n+m$. Among positive modes with even $n+m$, the only product that can fail to vanish for $\nu>1/2$ is $n=m=1$; boundedness already kills its coefficient.

### 3.4 Finish the contradiction

We have proved $hk=0$ at every vertex. On each full closed side (including its two vertices), a nonzero continuous product would have a nonzero maximum or minimum in its interior. Section 3.1 excludes this, so $hk=0$ on every side.

Choose any open side. A nonzero eigenfunction cannot have identically zero Dirichlet trace on an open subinterval together with its Neumann condition: even reflection and analytic Cauchy uniqueness would force it to vanish throughout the connected domain. Thus there is a subinterval where $h\ne0$. There $k=0$, and $k$'s zero Neumann data force $k\equiv0$, a contradiction. This proves Statement P.

**Scope:** Statement P holds at any positive common eigenvalue, does not require $h,k$ to be orthogonal, and does not use simple connectivity. Only the later first-eigenline application needs that topology.

## 4. Surjectivity of the traceless shape derivative at a double polygonal eigenvalue

Let $E_\lambda$ be a two-dimensional eigenspace on $P$, with the $L^2(P)$ inner product. Allow smooth compactly supported ambient vector fields $V$ that vanish near all vertices. The deformation is $\Phi_t(x)=x+tV(x)$. For sufficiently small $t$, it is a diffeomorphism, and $P_t=\Phi_t(P)$ is a Lipschitz domain with unchanged corner neighborhoods and possibly curved open sides.

Pull the energy and mass forms back to $H^1(P)$:

\[
a_t(v,z)=\int_P(D\Phi_t^{-T}\nabla v)\cdot(D\Phi_t^{-T}\nabla z)J_t,
\qquad
b_t(v,z)=\int_PvzJ_t.
\]

Their first derivatives exist in form norm. On $E_\lambda$, set $q_V=a'_0-\lambda b'_0$. Explicitly,

\[
q_V(v,z)=\int_P\left[
\operatorname{div}V(\nabla v\cdot\nabla z-\lambda vz)
-\nabla v\cdot(DV+DV^T)\nabla z\right].                 \tag{4.1}
\]

No boundary trace is needed for (4.1). Since $V$ vanishes near the vertices, integration by parts takes place only where the eigenfunctions are smooth up to a straight side. The cross-stress tensor has zero interior divergence, and the Neumann conditions give

\[
q_V(v,z)=\sum_e\int_e(V\cdot n)
       ((\partial_\tau v)(\partial_\tau z)-\lambda vz)\,ds. \tag{4.2}
\]

The normal speed on any compact subinterval of any open side can be prescribed arbitrarily by such a $V$.

**Claim:** $V\mapsto q_V^0\in\operatorname{Sym}_0(E_\lambda)$ is onto.

Otherwise a nonzero traceless symmetric matrix annihilates its image. Diagonalize that matrix in an orthonormal basis $f,g$, with diagonal entries $\rho,-\rho$, $\rho\ne0$. Then

\[
q_V(f,f)-q_V(g,g)=0\quad\hbox{for every allowed }V.
\]

Local normal-speed tests in (4.2) imply

\[
f_\tau^2-\lambda f^2=g_\tau^2-\lambda g^2
\]

on every open side. Put $h=f+g$, $k=f-g$, both nonzero. This is exactly $h_\tau k_\tau=\lambda hk$, contradicted by Statement P.

Thus the proposed surjectivity mechanism in scout Section 2.7 **is proved for every polygon**, including nonsymmetric and nonconvex polygons. This is not restricted to symmetry-forced multiplicity.

## 5. Every first eigenline of a simply connected polygon is reachable

### 5.1 Select the lower branch by a variational argument

Let $P$ be simply connected and let $\mu=\mu_1^N(P)$ be double. Section 2 (or Judge–Mondal Corollary 5.4) ensures the first-positive cluster is exactly two-dimensional. Fix any unit $u\in E(P)$. By Section 4 choose $V$ such that $q_V$ has $\mathbb Ru$ as its **simple lowest** eigenline on $E(P)$, with eigenvalues $\alpha<\beta$. The scalar part of $q_V$ is immaterial.

Let $\mu_t=\mu_1^N(P_t)$, $t>0$, and pull a normalized first eigenfunction back to $v_t\in H^1(P)$. Normalize $b_t(v_t,v_t)=1$, $b_t(v_t,1)=0$. Uniform equivalence and $O(t)$ closeness of the energy and mass forms, together with the variational principle on the quotient by constants, give $\mu_t=\mu+O(t)$.

Every sequence $t\downarrow0$ has a subsequence with $v_t\to v\in E(P)$ strongly in $H^1(P)$, $\|v\|_2=1$. To see strong convergence, first use weak $H^1$ and strong $L^2$ compactness and pass to the weak equation. The energies converge to $\mu$, the energy of the normalized limiting minimizer; weak convergence plus convergence of gradient norms gives strong $H^1$ convergence.

Take a subsequence along which $\delta_t=(\mu_t-\mu)/t\to\delta$. For $z\in E(P)$, the weak eigenvalue equation and the equality $a_0(v_t,z)=\mu b_0(v_t,z)$ imply

\[
\delta_t b_0(v_t,z)
 = (a'_0-\mu b'_0)(v_t,z)+o(1).
\]

Hence $q_V(v,z)=\delta\langle v,z\rangle$. Thus $v$ is an eigenvector of $q_V$.

For the complementary upper bound, test the first-positive Rayleigh quotient with

\[
u_t=u-\frac{b_t(u,1)}{b_t(1,1)}.
\]

Since $b_0(u,1)=0$, the subtracted constant is $O(t)$. It changes no energy and changes the mass only at order $t^2$. Therefore

\[
\mu_t\le\mu+tq_V(u,u)+O(t^2)=\mu+t\alpha+O(t^2).
\]

It follows that $\delta\le\alpha$, while the eigenvector equation gives $\delta\in\{\alpha,\beta\}$. Thus $\delta=\alpha$ and $v=\pm u$. Choose signs by $\langle v_t,u\rangle>0$. Then all subsequences converge to $u$.

Moreover $\mu_t$ is simple for all sufficiently small positive $t$. Otherwise choose two orthonormal first eigenfunctions along a sequence $t_j\downarrow0$. Both limits would lie in $\mathbb Ru$, while their limiting inner product would remain zero and both norms one, an impossibility.

Returning to physical coordinates gives $u_t\to u$ locally in $L^2(P)$, and then in $C^\infty_{\rm loc}(P)$ by interior elliptic estimates. Every compact subset of $P$ is contained in $P_t$ for small $t$.

This proves actual eigenline selection. Generic simplicity alone would not establish it.

### 5.2 Smooth each selected simple domain: checked approximation contract

For a fixed sufficiently small $t>0$, apply Ball–Zarnescu to $D=P_t$. Its inner smooth approximants $D_\varepsilon$ preserve simple connectivity. Their uniformly bi-Lipschitz maps $F_\varepsilon:D\to D_\varepsilon$ equal the identity off a shrinking collar.

Here is the spectral argument, avoiding any unstated convergence of eigenlines:

* Restrict a normalized first eigenfunction of $D$ to $D_\varepsilon\subset D$, subtract its new mean, and use it as a trial function. Since the omitted set shrinks to the boundary, this proves $\limsup\mu_1^N(D_\varepsilon)\le\mu_1^N(D)$.
* For normalized minimizing eigenfunctions $w_\varepsilon$ on $D_\varepsilon$, the pullbacks $z_\varepsilon=w_\varepsilon\circ F_\varepsilon$ are uniformly bounded in $H^1(D)$. A subsequence converges strongly in $L^2(D)$ and weakly in $H^1(D)$.
* The Jacobians $J_\varepsilon=|\det DF_\varepsilon|$ are uniformly bounded above and below and equal one eventually at each interior point. Strong $L^2$ convergence and dominated convergence in
  $\int_Dz_\varepsilon^2J_\varepsilon=1$,
  $\int_Dz_\varepsilon J_\varepsilon=0$
  preserve norm and mean in the limit.
* On each fixed compact subset of $D$, the maps are eventually the identity. Energy lower semicontinuity there and exhaustion imply that the limit is a normalized minimizer for $D$, and the eigenvalues converge.
* Interior elliptic estimates upgrade convergence in physical coordinates to $C^\infty_{\rm loc}(D)$.

Since $\mu_1^N(D)$ is simple, signs select its prescribed eigenfunction. A two-orthonormal-limits contradiction also shows that the approximants' first-positive eigenvalues are eventually simple.

Finally choose $t_j\downarrow0$ and then choose $\varepsilon_j$ sufficiently small to approximate $u_{t_j}$ on the first $j$ compact sets of an exhaustion, in the first $j$ derivative norms. The resulting bounded simply connected $C^\infty$ domains have first-positive eigenfunctions converging to $u$ in $C^\infty_{\rm loc}(P)$.

If $\mu_1^N(P)$ is simple, Section 5.2 applies directly with $D=P$.

**Theorem E:** For every bounded simply connected polygon $P$, $\mathcal L(P)=E(P)$, with the scout's definition of $\mathcal L$.

The final sequence is not asserted nested or contained in $P$. It converges geometrically to $P$ and eventually contains every compact subset of $P$, precisely as required in the scout's Definition 2.2. Each smoothing is inner relative to its already perturbed domain. A stronger demand for a nested exhaustion inside the original polygon is not proved here and is unnecessary for the hot-spots implication.

## 6. Conditional strict hot spots for every simply connected polygon

Assume the pinned corpus's family 369 theorem. Let $0\ne u\in E(P)$. By Theorem E, $u$ is a local smooth limit of smooth-domain first-positive eigenfunctions with nonvanishing gradient.

This immediately excludes strict interior local extrema: a strict local maximum gives a small ball whose boundary values are uniformly lower, and the approximating functions would then have an interior maximum. It also excludes nonzero-index isolated critical points by local degree stability.

For clarity, the additional argument needed to exclude a non-strict *global* interior extremum is as follows.

Suppose $M=\sup_Pu$ is attained and $S=\{u=M\}\cap P$. Then $M>0$. If $P\setminus S$ had distinct components $U_1,U_2$, set $f_i=(u-M)1_{U_i}\in H^1(P)$. The membership follows from local Lipschitz continuity across the zeroed interfaces, with gradient $1_{U_i}\nabla u$, and global $L^2$ bounds. Testing the weak equation gives

\[
\mu\|f_i\|_2^2-\|\nabla f_i\|_2^2
 =\mu M\int_{U_i}(M-u)>0.
\]

A nonzero mean-zero combination of $f_1,f_2$, whose supports are disjoint, has Rayleigh quotient below $\mu$, a contradiction. Thus $P\setminus S$ is connected. This checks scout Lemma R and does not need boundary smoothness.

At a point of $S$, the negative-semidefinite Hessian has trace $-\mu M<0$. In **two dimensions**, its rank is one or two. In the rank-one case the analytic implicit function theorem applied to a transverse derivative reduces the maximum set locally to the zero set of a one-variable analytic function. Consequently each point of $S$ is isolated or belongs to an analytic embedded arc, and the nonisolated part is relatively closed. Isolated points would be strict local maxima and have already been excluded. Thus any component of $S$ is a closed embedded one-manifold, hence a proper circle or line in the Jordan domain $P\cong\mathbb R^2$. Either separates the domain by the Jordan theorem (one-point compactify a proper line). Since $S$ has empty interior, both sides contain points outside $S$, contradicting connectedness of $P\setminus S$.

Apply the same argument to $-u$. Boundary continuity and compactness give

\[
\boxed{\quad
\min_{\partial P}u<u(x)<\max_{\partial P}u
\quad\text{for every }x\in P,\quad 0\ne u\in E(P).
\quad}
\]

Thus the full strict hot-spots statement holds for **all bounded simply connected polygons**, under the corpus premise. Degenerate index-zero interior critical points are not excluded by this proof, so do not claim full gradient nonvanishing on polygons.

Two corrections to the scout remain necessary in the parent's integration: its opening polygon/convex-domain inclusion must retain the simple-eigenvalue qualification unless replaced by the polygon result here; its Lemma T must explicitly be planar. Theorem E now removes that simplicity qualification for polygons, but not for arbitrary convex Lipschitz domains.

## 7. What remains for arbitrary Lipschitz domains

The multiplicity issue is now sharply reduced to a double eigenspace, by Section 2. The volume form (4.1), and the variational selection proof in Section 5.1, remain valid on every Lipschitz domain. Therefore surjectivity of $V\mapsto q_V^0$ would finish the all-Lipschitz problem.

The missing result is a Lipschitz replacement for Statement P. One must exclude a zero weak boundary traction for a cross-stress tensor without simply assuming a classical identity for tangential derivatives. Even if a suitable almost-everywhere identity were justified, the elementary smooth-boundary maximum argument does not automatically follow: an absolutely continuous boundary function can attain an extremum at a nondifferentiability point.

For a concrete warning about that last inference, let $\varphi(s)$ be a periodic triangular-wave function with $|\varphi'|=1$ almost everywhere, and put $h(s)=k(s)=e^{\sqrt\lambda\varphi(s)}$. Then $h'k'=\lambda hk$ almost everywhere on the circle, despite (hk) being positive and attaining maxima. These are **not claimed to be Neumann eigenfunction traces**. They show exactly why mere absolutely continuous trace regularity plus the identity is insufficient. The polygon corner expansion supplies the missing PDE constraint at the nondifferentiability points; no analogue has been proved here for an arbitrary Lipschitz graph.

Partial smoothing followed by smooth-domain transversality is also insufficient as stated. The inverse controllability norm can diverge as smoothing is removed; the spectral splitting error must be small relative to the available control. No uniform estimate, or alternative nonlinear winding argument forcing every line to be reached, was obtained in this review.

Similarly, a generic-simplicity theorem only produces simple eigenvalues near a multiple one. Even a dense set of simple symmetric matrices can approach a double scalar matrix along a family whose lower eigenline is always the same; for example $\operatorname{diag}(0,t^2)$ as $t\to0$. It does not establish arbitrary eigenline selection.

**Disposition of the original all-Lipschitz request:** not proved. **Complete special case obtained:** all simply connected polygons, regardless of multiplicity or symmetry. No obstruction to the truth of the all-Lipschitz conjecture is claimed.

## 8. Validation and novelty limits

* Source statements were read, with the contracts listed in Section 1. The standing smooth hypothesis of the corpus multiplicity proposition was not silently dropped.
* The corner proof was checked separately for convex angles, reentrant angles, the $3\pi/2$ resonance, and angles approaching $2\pi$. The strict inequality $\nu>1/2$ is essential; slit tips of angle $2\pi$ lie outside the polygonal Lipschitz hypothesis.
* The localized shape form was derived from pullback of energy and mass; its boundary conversion uses support away from all vertices. No singular corner boundary integral is taken.
* The lower-branch selection proof includes the change of mean under deformation, distinguishes positive from negative $t$, and proves simplicity after splitting rather than assuming it.
* Smooth approximation uses Ball–Zarnescu's exact topology and uniform bi-Lipschitz contracts, and a direct compactness proof. It does not identify an arbitrary eigenfunction with an arbitrary limit when multiplicity is present.
* [`../experiments/hotspots_multiplicity_r2/check_corner_parity.py`](../experiments/hotspots_multiplicity_r2/check_corner_parity.py) checks the two-edge parity cancellation and the resonant exponent using exact rational arithmetic. Its [output](../experiments/hotspots_multiplicity_r2/results.json) passed. This is an algebra check, not numerical evidence for the theorem.
* The subsequent [novelty review](hotspots-polygon-novelty-r3.md) identified the smooth-boundary argument explicitly: Marrocos–Pereira, [arXiv:1310.5178](https://arxiv.org/pdf/1310.5178), Lemma 2 (attributed there to Uhlenbeck), and the $f\pm g$ polarization in the proof of Theorem 9, case ii. The lemma's flow proof gives pointwise $fg=0$; for eigenfunction traces, Cauchy uniqueness supplies the required contradiction. Traceless transversality is the standard SAH2 property, and lower-branch selection is standard perturbation theory once it holds. Hillairet–Judge's [generic spectral simplicity of polygons](https://arxiv.org/pdf/math/0703616), Theorem 1.1, remains weaker than per-line control. A bounded search found no polygon version of the short vertex lemma, but did not establish literature priority. This is a modest technical extension, not the significant novel mechanism requested by the user.

Review status: the independent novelty reviewer also checked Sections 2–6 and found no gap. The dedicated [adversarial proof review](hotspots-polygon-proof-r3.md) also accepted the mathematics and supplies the differentiated infinite-tail estimate, isolated-cluster gap, and precise smoothing argument. Preserve this as a technical note with corrected attribution, not as fulfillment of the research objective. The all-Lipschitz claim remains explicitly open.
