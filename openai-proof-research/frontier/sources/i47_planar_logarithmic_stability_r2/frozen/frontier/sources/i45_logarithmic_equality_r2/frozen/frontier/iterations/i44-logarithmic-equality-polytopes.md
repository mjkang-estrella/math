# I44 — independent equality audit and two polytopal constructions

**Disposition: I43's audited mathematical partials PASS ORIGINAL WITHOUT REPAIRS. A newly verified current primary, Liu–Sun–Xiong, arXiv:2610.10152v2 (8 October 2026), already proposes the full equality classification, including arbitrary centered bodies. Its actual tensor and boundary proof supplies the previously missing mechanism. Section 5 gives a detailed symmetric specialization and checks its dependencies. This is an attributed technical reduction, not an I44 discovery or an assumption that this external manuscript is true. No substantial finding is nominated; the count remains 6/10.** The authors explicitly describe their manuscript as a proposed proof whose independent human verification is incomplete; the symmetric reduction here still needs the parent's independent proof review.

Before that late primary identification, two distinct constructions yielded useful necessary information for all polytopal equality paths: fixed facet centroids divided by support widths, including persistent nonsimple strata; and the hard-boundary limit of the scalar soft covariance defect on irredundant facets. Both are proved below and retained as technical partials. The latter identifies the lost 1/q scale in a normalized-score approach. The current primary avoids that loss by completing squares against the unnormalized score and retaining the Gaussian regularizer. The follow-up now concerns quantitative rigidity: Section 6 proves that a uniform **quadratic** deficit bound by distance to the entire equality class is false, even for planar hexagons. A possible cubic-or-weaker uniform bound remains unproved. This obstruction does not count as a substantial finding.

All OpenAI source operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are premises, not targets of an upstream audit. The complete user brief, unchanged I43 record and pertinent parent objections are frozen under `../sources/i44_logarithmic_equality_polytopes/`. Only this report and the assigned I44 source/experiment directories were written. No agents, shared edits, staging, commits or publication were used. New deductions here still require independent parent proof and significance reviews before any acceptance.

## 1. Target, dependencies, and current primary scope

For full-dimensional origin-symmetric bodies K,L in R^n and 0<λ<1, let

\[
 M_t=\mathcal W[h_K^{1-t}h_L^t],\qquad
 \Delta_\lambda=\log|M_\lambda|-(1-\lambda)\log|K|-\lambda\log|L|.
\]

The target E is Δλ=0 precisely when

\[
 \mathbb R^n=F_1\oplus\cdots\oplus F_m,\quad
 K=K_1+\cdots+K_m,\quad L=c_1K_1+\cdots+c_mK_m,
 \quad c_j>0,\quad \dim F_j>0,
\]

where K_j are symmetric relative convex bodies. Complementary subspaces need not be orthogonal; m=1 includes dilation. Dimension one is immediate. We attempt necessity for **all polytopes**, not only simple, generic or additionally symmetric ones. The current primary identified below handles the full convex-body target through a boundary-measure limit, without first requiring exact equality of approximating polytopes.

The pinned source L is `preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026`. Its `build/introduction.tex`, `thm:main`, supplies the inequality; `build/reduction.tex`, `prop:variance` and `eq:slabs`, supply arbitrary finite slab bounds, soft covariance contraction and the specified order of limits. `moment`, `identities`, `density`, `tensor`, and `variance` supply the actual fields and discarded squares. These do not state hard-boundary equality. Twelve selected source files are bound to the complete 13,223-entry, 749-manuscript tree. All 9,340 corpus text files are rehashed, including ignored files discovered with `rg --files --no-ignore`.

The bounded primary search was performed before construction and supplemented when references identified missing scope. Retained current records and full PDF text give:

* **Decisive late identification:** [Liu–Sun–Xiong, v2, 8 October 2026](https://arxiv.org/abs/2610.10152), *The centered logarithmic Brunn–Minkowski inequality*. The official abstract and explicit v2 PDF were retrieved successfully; Theorem 1.1 states exactly the direct-sum equality classification, in fact for centered bodies without symmetry. Sections 3.2–3.3 retain the tensor derivative remainder and pass to the boundary. Lemma 3.4 pays local moment-potential compactness using actual moment-measure stability and interior regularity results. These passages, not the abstract alone, underpin Section 5. The stated separate symmetric manuscript is unpublished and was not independently obtained; the current PDF contains the needed argument. The authors’ note on pp. 31–32 expressly labels the work a proposed proof requiring further scrutiny. Only the symmetric specialization is checked here; the full nonsymmetric theorem is not audited or assumed.

* [Lu, v3, 28 September 2026](https://arxiv.org/abs/2608.20730): E under n−2 common orthogonal reflections, with no regularity assumption, and the related revolution cases. The actual v3 labels include Corollary 1.5 and Theorem 1.8 for revolution statements; old snippets are not authoritative. The proof uses fiber equality and subspace symmetry.
* [Böröczky–De, v6](https://arxiv.org/abs/2101.02549): quantitative decomposition under n common linear reflections. This does not furnish unrestricted rigidity.
* [Putterman, v2](https://arxiv.org/abs/1909.03729): Alexandrov variation for arbitrary positive continuous bounds, and local/global polytope machinery. The support derivative does not require every bound to contact the Wulff body.
* [Hu–Ivaki, v1](https://arxiv.org/abs/2609.21670): the facet network, its support derivatives and C² regularity throughout the irredundant domain, including nonsimple polytopes (Proposition 8.5, Theorem 8.13). Its kernel theorem for the **ordinary support Hessian** and the baseline n−1 are not a kernel theorem for the **log-volume Hessian** at the threshold n. Its optimized lower bound n−1+1/(n−1) concerns locally minimizing eigenvalues, not the missing strictness at n.
* [Van Handel, final author version](https://web.math.princeton.edu/~rvan/logzon221121.pdf): nonsmooth local zonoid equality, Lemma 4.2's mixed-area identity and Lemma 4.3's use of a segment generating measure; Section 5 explains what its own smoothing argument loses.
* **Additional exclusion:** [Xi, v4, 14 November 2024](https://arxiv.org/abs/2307.04266), Section 4, already classifies **global log-Minkowski equality with a zonoid base and arbitrary symmetric comparison body**. Part 2 of the proof uses equality of cone-volume measures, equality in the projection Hölder inequality and the relation lemma to produce complementary blocks. This excludes zonotopes as a new global target. Corollary 2.7 equates several equality problems *assuming the inequality*; it does not solve their unrestricted equality classification.
* **Additional exclusions:** [Wang, v2, 4 November 2025](https://arxiv.org/abs/2510.19061), Theorem 1.3 and Proposition 4.5, gives conditional local rigidity for a smooth base with C² support and a C² comparison support. Its two-sided segment erosion argument needs adaptedness. [He–Liu, v1](https://arxiv.org/abs/2510.21530), Theorem 4 and proof of Theorem 3.1, gives conditional uniqueness for positive smooth even cone-volume density. Regularity makes the Wulff bound a genuine support function; their twice-differentiated equation and maximum argument then apply. Their nonsmooth variation formulas do not state E for discrete measures.

The parent-rejected aggregator identifier is not used as prior-art evidence. Its retained parent response remains frozen. The corrected identifier above is a separately verified primary; it must not be confused with the parent-rejected identifier. The earlier draft’s conclusion that no primary classifies all symmetric polytopes is withdrawn. This bounded search does not certify worldwide priority. Smooth conditional uniqueness, zonoid equality, the facet graph and the scalar spectral reformulation are credited as existing operations.

## 2. Independent audit of the original I43 partials

Each verdict concerns the original author bytes, which are preserved. RT and RP4 are outside this audit and are not used.

### 2.1 Proposition 2.1: PASS ORIGINAL WITHOUT REPAIRS

Put F(f)=log|W[e^f]| on even continuous functions. If A=W[e^f] and B=W[e^g], the logarithmic Wulff combination of A and B lies in W[e^{(1−t)f+tg}]. The accepted inequality gives concavity of F on this whole vector space.

Here is the potentially vulnerable contact argument explicitly. At a regular boundary point x of A, compactness of the sphere ensures an active constraint: otherwise e^f(u)−u·x has a positive minimum, making x interior. The normal of an active constraint must be the unique normal N_A(x). Thus e^f(N_A(x))=h_A(N_A(x)). Regular boundary points have full boundary area, so contact holds S_A-almost everywhere. This does not assert contact for all directions.

For k(t,u)=e^{f(u)+tg(u)}, the difference quotient converges uniformly to e^f g. Putterman's Lemma 2.1 applies to this positive bound, including inactive directions, and gives

\[
 DF(f)g=|A|^{-1}\int e^f g\,dS_A
       =n\int g\,d\nu_A,\qquad \nu_A=h_A dS_A/(n|A|).
\]

This is a continuous linear functional in g. A concave function's directional derivative is a global upper support: restrict to a line and use its decreasing chord slopes. If F is affine on [f,g], the upper support at f also contacts g. At a point where the two-sided directional derivatives exist, any upper supporting functional equals the derivative, by testing both signs of every direction. Thus all derivatives on the equality segment agree. Testing all even continuous functions distinguishes these even measures. Conversely, equal derivatives at the endpoints squeeze F(g)−F(f) between equal numbers and force affinity. An interior chord equality forces affinity on the entire segment by elementary concavity. Contact plus continuity upgrades almost-everywhere contact to contact on the support of the common measure.

No Fréchet differentiability, strict concavity or inverse map theorem was assumed.

### 2.2 Common facets, weights, and easy direction: PASS ORIGINAL WITHOUT REPAIRS

For an equality polytope pair, every intermediate S_M has finite support equal to the endpoint facet normals. The standard discrete surface-area characterization makes M a polytope: Minkowski existence gives a polytope with that discrete surface area measure, and uniqueness identifies M up to translation, removed by symmetry. Thus there are exactly the same true signed facets throughout. For one unit normal u_i per antipodal pair,

\[
 P(t)=\{x:|u_i\cdot x|\le h_i(t)=a_i e^{b_i t}\},\quad
 V(t)=Ce^{st},\quad
 w_i=2h_iA_i/V>0,\quad \sum_iw_i=n,\quad s=\sum_iw_i b_i.       \tag{2.1}
\]

A_i is the area of the positive facet. The common finite list has positive minimum weight on this exact path, but that makes no assertion about varying lists or approximation. Higher face incidences are not frozen by this argument.

For a complementary block decomposition, a GL(n) change makes blocks orthogonal. Block-direction constraints give one inclusion for M_t; Hölder applied to the block supports gives the other. Hence M_t=Σc_j^tK_j and its volume has the predicted exponential determinant. This proves sufficiency without restricting the original blocks to orthogonal ones.

### 2.3 Proposition 5.1: PASS ORIGINAL WITHOUT REPAIRS

Within a simple open chamber, vertices are linear in supports, and a fixed boundary triangulation gives a homogeneous degree-n **signed** volume polynomial Q. Distinct exponents α·b in Q(ae^{bt}) force, by exponential independence, a single nonzero monomial. Every true paired facet has ∂_iQ=2A_i>0, so all its exponents are positive integers. They sum to n, while the N normal directions must span R^n; hence N=n and all exponents are one. This gives a parallelotope. It does not allow generic perturbation of an equality pair. The original signed group constraints follow exactly by expanding Q and h_i∂_iQ=w_iQ. Neither the original proof nor this audit classifies their resonant solutions.

### 2.4 Hexagon: PASS ORIGINAL WITHOUT REPAIRS

In |a−b|<c<a+b, the two removed corner triangles give Q=4ab−(a+b−c)². With a=e^t,b=e^{−t},c=2−δ, 0<δ<1, this yields the original area and curvature 4δ/(4−δ²). At t=0 the paired weights are w_1=w_2=2/(2+δ), w_3=2δ/(2+δ). The **probability** cone-volume norm uses w_i/n, so for b=(1,−1,0) its square is 2/(2+δ), and the curvature/norm ratio is 2δ/(2−δ). This explains the normalization implicit in I43. The fixed ball bounds and genuine six sides hold. It defeats a uniform gap on this class, not a body-dependent kernel assertion or E.

### 2.5 Soft identities and limiting examples: PASS ORIGINAL WITHOUT REPAIRS

For ψ_i=(p_i·x/h_i(t))^q and U=Σψ_i,

\[
 -\partial_t^2\log Z_{q,\epsilon}
 =q^2[\sum b_i^2E\psi_i-\operatorname{Var}(\sum b_i\psi_i)].
\]

Differentiation under the Gaussian majorant is valid at fixed q,ε. For u=(Σb_iψ_i−EΣb_iψ_i)/σ, c_i=b_i√(Eψ_i), and (Tu)_i=E(uψ_i)/√(Eψ_i), one has ⟨c,Tu⟩=σ. Expansion proves I43's exact contraction-defect decomposition, including its separate σ=0 case. The source's dense tests approach u for each fixed q,ε; all retained nonnegative remainders are bounded by the dual defect. This supplies no parameter-uniform field compactness.

The Green kernel G_λ(t)=(1−λ)t for t≤λ and λ(1−t) otherwise gives the stated deficit by two integrations. Apply dominated convergence first q→∞ at fixed ε, then ε↓0; for arbitrary bodies apply direction exhaustion afterward. Only an integrated nonnegative defect tends to zero in equality.

At q=2, ε=0, the determinant expansion is a positive sum over bases and the curvature is twice the variance of basis slope sums. Circuit exchange proves that all sums agree exactly when b is constant on normal matroid components. No matroid claim about arbitrary hard constraints follows. For the genuine box endpoints, the three interpolated widths are (2^t,2^{−t},2(5/4)^t). Strict Hölder makes the diagonal inactive in the interior. Convexity of |·|^q and the product Gamma moment E|x/h|^q=1/q give 0≤log(Z_0/Z_1)≤ρ^q/q, including ρ=1 at endpoints. The example is an E equality, not a counterexample. All factors, signs and limit orders pass.

**Audit conclusion:** the mathematical partials survive. The current-literature discussion requires the Xi/Wang/He–Liu additions and the decisive Liu–Sun–Xiong identification in Section 1, not repairs to these proofs.

## 3. Attempt I: normal variation, facet moments and face compatibility

### 3.1 A finite stratification that includes persistent walls

Use all signed normals v_k and corresponding supports h_k(t)>0; opposite supports and slopes agree. For each independent n-tuple B, its candidate vertex is x_B(t)=V_B^{-1}h_B(t). Each feasibility event

\[
 v_j\cdot x_B(t)-h_j(t)=0                              \tag{3.1}
\]

is a sum of at most n+1 real exponentials. After equal exponents are collected, it is either identically zero or has at most n real zeros, counting multiplicity. The latter assertion follows by induction using Rolle's theorem after dividing by the smallest exponential. There are finitely many B,j, so there are finitely many event times. On every complementary open interval all vertex bases, incidences and face lattice are constant. Identically zero events remain as persistent nonsimple incidences. This does **not** discard nonsimple paths.

On such an interval select a basis for each vertex and a fixed pulling triangulation of every facet. The oriented determinants have constant sign. The volume, and each vector facet moment

\[
 J_i(h)=\int_{F_i(h)}x\,d\mathcal H^{n-1}(x),
\]

are restrictions of homogeneous polynomials, of degrees n and n respectively. For J_i this follows from the simplex integral: its centroid is the average of its vertices, multiplied by its (n−1)-dimensional volume. A fixed facet normal fixes the conversion from determinant to Euclidean area. One only claims polynomial representations **on this stratum**, not analytic continuation of geometric volume through a wall.

### 3.2 New necessary invariant on the whole equality path

**Proposition C (facet-centroid invariant).** Under the accepted finite-slab inequality, any exact equality path (2.1) satisfies

\[
 \frac{c_i(t)}{h_i(t)}=v_i^*\quad(0\le t\le1),             \tag{3.2}
\]

where c_i(t)=J_i(t)/A_i(t) is the centroid of its positive facet and v_i^* is fixed. The result covers resonances, nonsimple endpoints, isolated wall crossings and persistent nonsimple strata.

**Proof.** Perturb a representative unit normal u_i to u_i+ηr, with the opposite normal perturbed oppositely, keeping all widths fixed. The perturbed vectors need not remain unit; the finite-slab inequality explicitly permits this. Spanning and boundedness persist for small |η|. For each fixed t, the first normal variation is

\[
 \left.\partial_\eta\log V(t;\eta)\right|_0
       =-\frac{2}{V(t)}\int_{F_i(t)}r\cdot x\,d\mathcal H^{n-1}(x)
       =-w_i\,r\cdot\frac{c_i(t)}{h_i(t)}.                \tag{3.3}
\]

To justify the formula without simplicity, remove a small neighborhood of the facet boundaries, integrate the swept normal displacement −ηr·x there, and then let that neighborhood shrink. Near intersections of distinct facet hyperplanes the omitted swept overlaps have o(|η|) volume; all normals are fixed and finite and the body is bounded. Facet boundaries have zero facet area. This gives the formula from either sign. Equivalently it is the usual polyhedral shape first variation.

For every η the finite-slab deficit at t is nonnegative. At η=0 it vanishes. Its derivative in η is therefore zero. Using (3.3) and the fixed positive w_i proves that c_i(t)/h_i(t) is affine in t between its endpoint values, as a vector.

On any nonempty open stratum from §3.1, however,

\[
 \frac{c_i(t)}{h_i(t)}=\frac{J_i(h(t))}{h_i(t)A_i(t)}
       =\frac{2}{w_iC}e^{-st}J_i(ae^{bt})
\]

is a finite sum of real exponentials. Such a sum cannot be a nonconstant affine function: differentiate twice and use independence of the nonzero exponential rates. Thus the slope of the globally affine vector function is zero. This proves (3.2) on the entire interval, including its endpoints. ∎

The normal perturbations were used only to differentiate a **nonnegative deficit at its minimum**. We did not assert equality for perturbed normals. This additional parameter variation avoids the forbidden generic-slope perturbation.

On any stratum write J_i(h)=Σ_{|α|=n}d_{i,α}h^α, with vector coefficients d. In addition to I43's scalar resonance equations we now have

\[
 \sum_{\alpha\cdot b=r}d_{i,\alpha}a^\alpha
       =\frac{w_iC}{2}v_i^*\mathbf1_{r=s}.                \tag{3.4}
\]

These are vector moment cancellations forced by equality, not just volume and area cancellations. The divergence theorem also gives the consistency check Σ_i w_i v_i^*u_i^T=I. This check alone has no splitting content.

### 3.3 The ridge operator and the additional vector balance

For this paragraph index **all signed facets** by k. Write m_k=h_kA_k/V (so Σm_k=n), and for adjacent facets set

\[
 \kappa_{k\ell}=\frac{h_kh_\ell\,\mathcal H^{n-2}(F_k\cap F_\ell)}
                          {V\sin\theta_{k\ell}},
\]

setting it to zero for nonadjacent pairs. Opposite facets are never adjacent. The intrinsic formulas of Hu–Ivaki give, on the whole irredundant domain,

\[
 -D_z^2\log V[b,b]
 =\sum_{k<\ell}\kappa_{k\ell}(b_k-b_\ell)^2
       -n\sum_km_k(b_k-s/n)^2.                          \tag{3.5}
\]

Thus fixed cone weights on a path imply

\[
 \sum_\ell\kappa_{k\ell}(b_k-b_\ell)
       =nm_k(b_k-s/n).                                  \tag{3.6}
\]

This is the known spectral equation at n, not a new positive sum of squares. Connectivity only identifies the zero eigenvalue of the unshifted graph Laplacian; it does not identify its eigenspace at n.

Proposition C yields an additional vector equation. Let c_{kℓ} be the ridge centroid. Along each open stratum, motion of a facet in its tangent hyperplane has ridge speed

\[
 d'_{k\ell}=\frac{b_\ell h_\ell-b_kh_k\cos\theta_{k\ell}}
                         {\sin\theta_{k\ell}}.
\]

Differentiating its centroid gives

\[
 c'_k=b_kh_ku_k+\frac1{A_k}\sum_\ell
       \mathcal H^{n-2}(F_k\cap F_\ell)d'_{k\ell}(c_{k\ell}-c_k).
\]

Subtract the same facet first-moment formula for ordinary dilation at rate b_k, and use c'_k=b_kc_k from (3.2). The result is

\[
 \boxed{\ \sum_\ell\kappa_{k\ell}(b_\ell-b_k)(c_{k\ell}-c_k)=0.\ }   \tag{3.7}
\]

The area version is (3.6). The formulas remain true on persistent strata. At isolated events use continuity of the area and first moment measures of ridges; a disappearing ridge's measure and moment tend to zero, and surviving ridges converge. The C² support calculus does not require a fixed full fan.

This is the concrete result of Attempt I: exact scalar and vector equations, with the moment cancellations, valid for the entire polytopal target. It does **not** yet give E. In particular, a maximum principle cannot be applied to (3.7): at a maximal slope, all nonzero scalar coefficients have one sign, but the vectors c_{kℓ}−c_k can balance. Even a triangle has its centroid equal to the average of its three edge centroids. Nonzero positive coefficients therefore can annihilate this local vector sum. Global compatibility between these barycentric balances, (3.6), and the exponential evolution remains to be proved. This identifies where the new invariant stops, rather than merely relabeling the old scalar cancellation problem.

As an exact check, the hexagon's x-facet has c_1/a=(1,(c−a−b)/(2a)). At a=e^t,b=e^{−t},c=2−δ its second component has derivative δ/2 at zero. Proposition C excludes that whole path from equality for δ>0, consistently with its positive curvature. For every actual block equality, facet centroids scale with their own block and (3.2) holds, also after a nonorthogonal linear change.

## 4. Attempt II: an actual hard-boundary covariance limit

This calculation pays the scalar boundary limit and exposes the scale at which tensor traces would have to work. It does not replace moment fields by unjustified limiting fields.

Fix **any** full-dimensional symmetric polytope with irredundant representative unit normals u_i and supports h_i. Use

\[
 \psi_i=|u_i\cdot x/h_i|^q,\quad U_q=\sum_i\psi_i,\quad
 d\mu_{q,\epsilon}=Z_{q,\epsilon}^{-1}e^{-\epsilon|x|^2/2-U_q}dx.
\]

All following hard limits take q→∞ through even integers at fixed ε>0, **then** ε↓0. There is no direction exhaustion for this fixed polytope. Constants may depend on this polytope.

### 4.1 Facet and ridge measures

Let g_ε=e^{−ε|x|²/2}, Z_ε=∫_P g_ε, and μ_{P,ε}=g_ε1_P/Z_ε. Define the paired facet measure

\[
 d\beta_i^\epsilon=\frac{h_i}{Z_\epsilon}g_\epsilon
       (d\mathcal H^{n-1}|_{F_i^+}+d\mathcal H^{n-1}|_{F_i^-}),
 \quad w_i^\epsilon=\beta_i^\epsilon(\mathbb R^n).
\]

For i≠j let κ_ij^ε be h_i h_j/(Z_ε sinθ_ij) times the sum of the g_ε-weighted (n−2)-areas of all four signed facet intersections that are ridges; put zero for lower-dimensional intersections. At ε=0 abbreviate β_i,w_i,κ_ij. These are paired quantities; Σw_i=n.

**Proposition B (boundary moments).** For each fixed integer k≥1, as finite measures tested against bounded continuous functions,

\[
 q\psi_i^k\mu_{q,\epsilon}\ \rightharpoonup\ \Gamma(k)\beta_i^\epsilon,
 \qquad
 q^2\psi_i\psi_j\mu_{q,\epsilon}\ \rightharpoonup\ \beta_{ij}^\epsilon
 \quad(i\ne j),                                        \tag{4.1}
\]

where β_ij^ε is the weighted ridge measure just defined, with total mass κ_ij^ε. The same statements hold for tests |x|² in the first limit.

**Proof.** Slice orthogonally to u_i. In each sign of its normal coordinate put r=|u_i·x/h_i|^q. The measure qψ_i^k e^{−ψ_i} times the normal-coordinate differential becomes

\[
 h_i r^{k+1/q-1}e^{-r}\,dr.
\]

For r>0 the slice tends to the facet plane. At almost every point of that plane all other bounds are either strictly satisfied or strictly violated; boundaries have zero facet area because the constraints are irredundant. The remaining exponentials tend to the indicator of the facet. The r-integral tends to Γ(k).

For two different representatives slice by their two independent normal coordinates and make the two substitutions. The Jacobian is h_i h_j/(q² sinθ_ij); the two Gamma(1) integrals give one. A full-dimensional feasible subset of their affine intersection is a ridge and has exactly two incident true facets. Thus any further equality constraints occupy zero measure there. If there is no ridge, the feasible slice has zero (n−2)-area and the limit is zero. This also covers nonsimple vertices. A codimension-two face cannot have three distinct irredundant incident facets; this elementary fact is the precise reason redundant slabs would invalidate this step.

Dominated convergence is justified at fixed ε: Gaussian integration on each affine fiber is bounded uniformly in its offsets, also with a |x|² factor. The r-kernels are bounded by an integrable fixed polynomial times e^{−r}, and analogously for the two coordinates. The partition functions tend to Z_ε by the source's dominated convergence. Finally ε↓0 is harmless on the compact polytope and its finite faces. ∎

### 4.2 The full scalar defect, with the Gaussian correction paid

Let A_q=diag(Eψ_i), C_q=Cov(ψ_i,ψ_j), and D_q=A_q−C_q. The source states D_q≥0. Off the diagonal, (4.1) gives

\[
 q^2(D_q)_{ij}\longrightarrow w_i^\epsilon w_j^\epsilon-\kappa_{ij}^\epsilon.
\]

It remains to pay the cancellation of the two order-1/q diagonal terms. Integration of div(xψ_i e^{−ε|x|²/2−U_q}), and the analogous identity without ψ_i, gives the **exact** row-sum identity

\[
 \sum_j(D_q)_{ij}=\frac{\epsilon}{q}
                 \operatorname{Cov}(\psi_i,|x|^2).       \tag{4.2}
\]

In particular it is zero at ε=0, but we do not set ε=0 before taking the hard limit. By (4.1), after multiplication by q² the right side tends to

\[
 \epsilon r_i^\epsilon,
 \quad r_i^\epsilon=\int |x|^2d\beta_i^\epsilon
                         -w_i^\epsilon E_{P,\epsilon}|x|^2.
\]

These numbers stay bounded as ε↓0. The off-diagonal limits and row sums determine every diagonal entry. Hence q²D_q→H_ε, and

\[
 b^TH_\epsilon b=
 \sum_{i<j}(\kappa_{ij}^\epsilon-w_i^\epsilon w_j^\epsilon)(b_i-b_j)^2
                  +\epsilon\sum_i r_i^\epsilon b_i^2.
\]

Taking ε↓0 yields the exact finite matrix limit

\[
 \boxed{\ \lim_{\epsilon\downarrow0}\lim_{q\to\infty}q^2D_q=H_P,\qquad
 b^TH_Pb=\sum_{i<j}\kappa_{ij}(b_i-b_j)^2
              -n\sum_iw_i(b_i-\bar b)^2,\quad
 \bar b=\frac1n\sum_iw_i b_i.\ }                         \tag{4.3}
\]

This is precisely −D_z²log|P(e^z)| from the intrinsic support calculus, with no simplicity hypothesis. The Gaussian correction in (4.2) is essential to respecting the source's limit order. This proof is also independent of any assertion that second derivatives commute with pointwise volume convergence.

The form in (4.3) is **not** a positive edge sum. For example the irredundant octagon

\[
 |x|,|y|\le1,\quad |x+y|,|x-y|\le3/2
\]

has V=7/2 and paired weights (4/7,4/7,3/7,3/7). The x and y facets are nonadjacent, so their edge coefficient is −16/49. The two diagonal pairs likewise have coefficient −9/49. Each axis/diagonal pair has κ=6/7 and net coefficient 30/49. The matrix is positive semidefinite under L, but its individual terms have both signs. For a box, κ_ij=w_iw_j=1 for distinct coordinate pairs, so the whole defect vanishes despite nonconstant slopes. The limit therefore recovers the known spectral problem; it does not transfer the q=2 matroid proof.

### 4.3 True-facet concentration and the necessary defect scale

Take b≠0 and put f_q=Σb_iψ_i, σ_q²=Var(f_q), u_q=(f_q−Ef_q)/σ_q, and B_ε=Σw_i^ε b_i²>0. Proposition B gives

\[
 q\sigma_q^2\to B_\epsilon,\qquad
 u_q\mu_{q,\epsilon}\rightharpoonup0,\qquad
 u_q^2\mu_{q,\epsilon}\rightharpoonup
       \frac{\sum_i b_i^2\beta_i^\epsilon}{B_\epsilon}.    \tag{4.4}
\]

Indeed all cross products contribute only O(q^{−2}), while qEψ_i²→w_i^ε. Centering terms vanish in the last limit; the first signed measure even has total variation tending to zero, since E|f_q−Ef_q|=O(1/q). The last measure is a probability supported on the **actual facets**. After ε↓0 it remains so. Thus the score has no nonzero bulk L² limit; its entire unit L² mass moves to the boundary. Removing redundant constraints does not fix that problem.

There is a sharper conclusion at exactly the source's dual contraction. For this u_q set

\[
 T_qu=(E(u\psi_i)/\sqrt{E\psi_i})_i,\qquad
 d_q=1-\|T_qu_q\|^2.
\]

Using C_q=A_q−D_q gives the exact algebraic identity

\[
 d_q=\frac{b^TD_qb-b^TD_qA_q^{-1}D_qb}{b^TC_qb}.           \tag{4.5}
\]

At fixed ε, A_q=diag(w_i^ε)/q+o(1/q), D_q=H_ε/q²+o(q^{−2}), and b^TC_qb=B_ε/q+o(1/q). Consequently

\[
 \lim_{q\to\infty}q d_q=\frac{b^TH_\epsilon b}{B_\epsilon},
 \qquad
 \lim_{\epsilon\downarrow0}\lim_{q\to\infty}q d_q
       =\frac{b^TH_Pb}{\sum_iw_i b_i^2}.                 \tag{4.6}
\]

In particular **d_q→0 for every slope b**, not just for equality slopes. An argument that merely passes the normalized source squares to zero has discarded the information distinguishing a strict hexagon from a box. The density approximants can be chosen accurately enough at each fixed q,ε to retain (4.5); that choice still supplies no uniform inverse, normal trace, or control of the rescaled B,W fields.

This is the constructive obstruction furnished by Attempt II. An argument using these normalized scores must control their **1/q next-order dual defect**, retaining the ridge correction. Alternatively, the unnormalized-score completion in Section 5 controls different fields directly. Leading-order saturation and weak bulk limits are insufficient even on a fixed irredundant indecomposable polytope. Equations (4.1)–(4.6) are scalar/measure theorems, not an asserted tensor trace theorem.

## 5. Attributed full symmetric reduction from the current primary

This section follows Liu–Sun–Xiong v2, equations (3.10)–(3.16) and Section 3.3. It supplies the trace/compactness mechanism that Sections 3–4 alone do not. All moment identities and dense-range operations from the pinned symmetric source are premises. The additional limiting argument is explained here, not imported as an assumed theorem. We find no unpaid step in this symmetric specialization, subject to independent parent review of the analytic proof. This is **technical/duplicate** under the user's significance rule.

### 5.1 The derivative remainder and homogeneous completion

For the symmetric soft density μ=Z⁻¹exp(−V)dx, V=ε|x|²/2+Σψ_i, use the source's moment map x=∇φ(z), τ=D²φ, M=τ⁻¹, and compact test v. Put h=D_x²v, P=τh, B=τhτ, W=Px−div_zP, and u=𝒜(𝒜−I)v, where 𝒜=x·∇−τ:D². The source gives u=δ_μW and Eu=E(xu)=0. Let H_i=D²ψ_i, H=εI+ΣH_i, and

\[
 T(v)=E\operatorname{tr}((D_xW)^2)-E\operatorname{tr}(MBHB).
\]

The first trace is a matrix square, not a Hilbert–Schmidt square. The invariant nonnegative derivative norm is

\[
 \mathscr D(P)=\sum M_{ab}\tau_{kr}M_{\ell s}
 (\partial_{z_\ell}P_{ak})(\partial_{z_s}P_{br}).
\]

In a **constant** dual frame normalized to τ=I at the evaluation point, let C=D³φ, S=D_x³v, J_{ijk}=h_{ia}C_{ajk}, J^{12}_{ijk}=J_{jik}, and K_{akℓ}=∂_{zℓ}P_{ak}=S_{akℓ}+J_{kaℓ}. The pinned tensor calculation, before dropping its squares, gives

\[
 T(v)=E[\|M^{1/2}RM^{1/2}\|_{HS}^2
       +2|S+\mathrm{Sym}J|^2+\tfrac16|J-J^{12}|^2],
\]

where R=D_zW−B is symmetric. Full symmetrization and symmetry of S,C give the exact identity

\[
 2|S+\mathrm{Sym}J|^2+\tfrac16|J-J^{12}|^2
   =\tfrac12|K|^2+\tfrac32|\mathrm{Sym}K|^2.
\]

Consequently T(v)≥½E𝒟(P). On each region where κI≤τ≤ΛI, 𝒟(P)≥κΛ⁻²|D_zP|². No differentiated moving frame, or global bound independent of ε, is used.

Now take arbitrary coefficients β_i, set F=Σβ_iψ_i, U=F−EF, γ_i=β_i/q and D=Σβ_i²Eψ_i−EU². Symmetry makes E(xF)=0. Homogeneity and source adjunction give, with a_i=Eψ_i and d_i=E(uψ_i),

\[
 E\operatorname{tr}(\tau H_i)=qa_i,\quad
 E\operatorname{tr}(BH_i)=E(W\cdot\nabla\psi_i)=d_i,
\quad E(x^TH_ix)=q(q-1)a_i,\quad E(x^TH_iW)=(q-1)d_i.
\]

Polynomial moments and an expanding cutoff justify the noncompact Stein test. Expanding the following squares then proves the **exact** identity

\[
\begin{split}
 D+\|u-U\|_2^2={}&T(v)+\epsilon E[\operatorname{tr}(MB^2)+|W|^2]\\
 &+\sum_i E\operatorname{tr}\{M(B-\gamma_i\tau)H_i(B-\gamma_i\tau)\}\\
 &+\sum_i E[(W-\gamma_ix)^TH_i(W-\gamma_ix)].             \tag{5.1}
\end{split}
\]

Every term on the right is nonnegative. The combined i-th square has cross term −2β_id_i and constant β_i²a_i. Also Eu²=E(WᵀHW)+Etr((D_xW)²). These observations verify (5.1) directly. Dense range chooses a compact v with arbitrarily small ||u−U|| at **each** fixed q,ε. No uniform inverse estimate is asserted.

### 5.2 A diagonal limit with an actual uniform field bound

Normalize |K|=|L|=1. Proposition 2.1 gives log|M_t|=0, identical cone-volume measures and common normal support. Let f=log(h_L/h_K). Choose symmetric increasing finite direction sets with dense union, including the coordinate directions. Their outer Wulff polytopes Q_m(t) decrease to M_t, between common balls rB,RB. Log volumes decrease uniformly to zero by Dini, using continuity in t.

Fix ε_j↓0. Choose m_j so the outer error is at most ε_j. Next choose even q_j, for this finite set and this ε_j, so the soft log integral error is at most ε_j, and q_j≥j(1+log(N_j+1)). These choices follow from the source's sequential limits and compact t-uniform domination. They constitute a diagonal subsequence of justified limits, not an interchange of limits. Write G_j(t)=log Z_j(t). Then |G_j|≤Cε_j uniformly and G_j is concave. Secant bounds on [1/3,2/3] give a t_j there with −G_j''(t_j)≤Cε_j and |G_j'(t_j)|≤Cε_j. Pass to t_j→t_* and C=M_{t_*}.

Use one-sided powers for signed directions, or equivalently pair opposite powers to obtain the pinned even |p·x/h|^q potential. All one-sided formulas below are just a splitting of an even power; the sum remains smooth. At t_j put

\[
 F_j=-q_j\sum_i f(p_{i,j})\psi_{i,j},\qquad
 D_j=q_j^2\sum_i f(p_{i,j})^2E\psi_{i,j}-\operatorname{Var}(F_j)
      =-G_j''(t_j)\le C\epsilon_j.
\]

We also have EF_j=−G_j'(t_j)→0. On compact subsets of int C all ratios are ≤ρ<1; hence derivatives of Σψ_i of any fixed order k are bounded by C_kN_jq_j^kρ^{q_j−k}→0. Outside C a fixed violated direction from the dense union forces the density to zero. The coordinate directions supply a common integrable superlinear tail majorant, also after multiplication by every fixed polynomial. Thus μ_j→1_Cdx in L¹ and W₁, all polynomial moments converge, and V_j→0 locally in every C^k(int C).

The moment potentials can be translated so that φ_j→φ locally in every fixed C^k, with ∇φ a diffeomorphism R^n→int C. Here is the paid compactness argument, corresponding to the primary's Lemma 3.4:

* Berman–Berndtsson, Theorem 1.1, applies to the centered uniform measure on **any** full-dimensional C and gives a smooth strictly convex entire moment potential. It requires no boundary smoothness.
* Bonnet–Rubinstein, Theorem 1.3, applies to the centered probabilities μ_j and μ. They have finite first moments, uniform bounded first moments, and a positive directional first-moment lower bound inherited from μ. Its W₁ stability supplies L¹ convergence of source densities after translations. An index with μ_j=μ uses translation uniqueness.
* Cule–Samworth, Proposition 2, gives uniform-on-compact convergence of log-concave densities to the continuous positive e⁻φ. Logs and convex difference quotients give φ_j→φ in C¹ locally.
* On any source compact set, the images ∇φ_j stay in a fixed compact subset of int C. The equation det D²φ_j=Z_j exp(−φ_j+V_j(∇φ_j)) gives two-sided determinant bounds. The strictly convex limit and C¹ convergence supply a uniform strict-convexity modulus at every fixed separation and nested compact sections. Interior section estimates give C¹,α; the right side becomes Hölder. Figalli–Jhaveri–Mooney Theorem 1.1 then gives C²,α with that controlled modulus. The determinant lower bound supplies a positive Hessian lower bound; differentiating the logarithmic equation and using Schauder estimates gives every fixed order. This is local compactness, independent of the diverging global cap 4/ε_j.

These actual primary dependency passages were retrieved and read. With v_j chosen so ||u_j−(F_j−EF_j)||₂≤ε_j, (5.1) now gives

\[
 T(v_j)\to0,\qquad \sup_j\int|W_j|^2d\mu_j<\infty.       \tag{5.2}
\]

The second bound follows because D_j=O(ε_j) and the regularizer is **ε_j**E|W_j|². This is exactly the control absent from the normalized-score approach. The local moment bounds and derivative remainder give D_zP_j→0 in L² on every source ball. Poincaré gives P_j−A_j→0, with A_j its mean on B₁. From W_j=P_jx_j−div P_j and (5.2), A_j is bounded: ∫_{B₁}x_jx_jᵀdz tends to a positive definite matrix since ∇φ(B₁) is open. After subselection, A_j→A. Comparing averages on larger balls yields

\[
 P_j\to A,\quad W_j\to A\nabla\varphi\quad\hbox{in }L^2_{loc}(dz),
 \qquad W_j(x)\to Ax\quad\hbox{in }L^2_{loc}(\operatorname{int}C).
\]

Since B_j=P_jτ_j is symmetric, Aτ=τAᵀ throughout the source space.

### 5.3 Identifying the hard boundary instead of assuming traces

For signed one-sided powers define the positive measure

\[
 \Lambda_j(dx,du)=\sum_i q_j\psi_{i,j}(x)\mu_j(dx)\delta_{p_{i,j}}(du).
\]

Radial integration by parts gives its mass n−ε_jE|x|² and second moment (n+2)E|x|²−ε_jE|x|⁴. Hence it is tight with uniformly integrable first moments. For compact smooth g,

\[
 \int g\,d\Lambda_j=\int(ng+x\cdot\nabla g-\epsilon_jg|x|^2)d\mu_j
   \longrightarrow\int_{\partial C}g\,h_C(\nu)\,dS.
\]

Here dS on the boundary denotes Hausdorff boundary area, not the spherical surface-area measure. On a region with slack p·x≤(1−δ)e^{a_{t_*}(p)}, its Λ_j mass tends to zero by N_jq_j(1−δ/2)^{q_j}→0. Thus a joint limit is supported on contact pairs (x,p) with x∈∂C and p·x=h_C(p)=e^{a_{t_*}(p)}. The normal is unique at boundary-area-almost every x. Therefore

\[
 \Lambda_j\rightharpoonup h_C(\nu(x))\,dS(x)\,\delta_{\nu(x)}(du),
\quad F_j\mu_j\rightharpoonup-f(\nu)h_C(\nu)dS|_{\partial C}.
\]

Adjunction ∫u_jg dμ_j=∫W_j·∇g dμ_j passes to the limit. Indeed, on an interior compact set use the local L² convergence. On its complement Cauchy–Schwarz and (5.2) bound the error by a constant times μ_j(boundary layer plus exterior)^{1/2}, which tends to zero as the layer shrinks. The L² test error and EF_j→0 also disappear. Consequently

\[
 \int_C Ax\cdot\nabla g\,dx=-\int_{\partial C}g f(\nu)h_C(\nu)dS.
\]

Testing first in the interior proves tr A=0. Boundary integration by parts then proves

\[
 Ax\cdot\nu=-f(\nu)h_C(\nu)\quad\text{boundary-area almost everywhere}.   \tag{5.3}
\]

This derives the normal flux and pays the trace passage; it assumes neither a segment representation nor a uniform positive facet mass in the approximation.

### 5.4 Splitting and scope

The relation Aτ=τAᵀ makes A similar to a real symmetric matrix. A constant dual linear transformation makes A symmetric. The same relation now says D²φ commutes with A. For distinct eigenspaces E_i, all mixed Hessian blocks vanish; since φ is defined on the whole product space, φ(z)=constant+Σφ_i(z_i). Its gradient image and closure therefore split: C=⊕C_i. Boundary normals of this product lie in the union of E_i. Proposition 2.1 gives the same normal support for K,L,C, so reconstruction from supporting halfspaces separates K=⊕K_i and L=⊕L_i on the same spaces. On the i-th normal support, (5.3) says f=−λ_i, the negative eigenvalue of A. Almost-everywhere equality extends to that support by continuity, hence L_i=e^{−λ_i}K_i. Undoing the linear transformation allows nonorthogonal complementary subspaces. Undoing endpoint volume normalization restores arbitrary dilation factors. Sufficiency was audited in Section 2.

This reduction handles **all symmetric polytopes, all resonances, all nonsimple configurations and all arbitrary symmetric convex bodies at once**. Exact polytopal equality is never asserted for approximants. It does not prove the stronger local statement K that every zero-curvature direction at one body splits: whole-path affinity was essential to the O(ε_j) selection. K remains unproved here, with no counterexample produced.

For completeness, two earlier shortcuts remain invalid even though the primary now supplies a different proof. Xi's zonoid argument uses a segment generating measure absent for arbitrary polytopes. Wang's adaptedness cannot be omitted: if P=[−1,1]² and I=[−(1,1),(1,1)], then P÷tI=[−1+t,1−t]²; at v=(1,−1), the support erosion derivative is 2 whereas h_I(v)=0. Neither is an obstruction to the correctly retained tensor argument.

## 6. Constructive pivot: a cubic obstruction to quantitative equality

A genuine remaining target is a uniform power estimate on a ball-bounded class, allowing arbitrarily many facets and arbitrary bodies. Fix n≥2, 0<r<R and 0<τ<1/2. Let 𝓔 be the set of all origin-symmetric full-dimensional equality pairs described by E, and define

\[
 d_{\mathcal E}(K,L)=\inf_{(K',L')\in\mathcal E}
       \max\{d_H(K,K'),d_H(L,L')\}.
\]

One can ask for α<∞ and c>0 depending only on n,r,R,τ such that Δ_λ(K,L)≥c d_𝓔(K,L)^α whenever rB⊂K,L⊂RB and λ∈[τ,1−τ]. No such finite exponent is proved here. Compactness plus the equality classification gives only a qualitative modulus: otherwise a convergent sequence of pairs with deficit→0 and distance bounded below would limit to an equality pair. Continuity follows from uniform positive supports and Wulff inclusions; distance to any set is 1-Lipschitz. This is a standard technical consequence, not a finding.

**Proposition Q (quadratic rigidity fails already in dimension two).** There are symmetric six-facet pairs K_t,L_t, contained between fixed balls, for which

\[
 d_{\mathcal E}(K_t,L_t)\asymp t,\qquad
 \Delta_{1/2}(K_t,L_t)=\tfrac12t^3+O(t^4),\qquad t\downarrow0.       \tag{6.1}
\]

Thus any estimate of the indicated form for a class containing these pairs must have α≥3. This is a quantitative obstruction, not an E counterexample and not a substantial finding under the brief.

**Proof.** Define P_δ(s) by |x|≤e^s, |y|≤e^{−s}, |x+y|≤2−δ. Set δ=t, K_t=P_t(−t), L_t=P_t(t). For all sufficiently small t>0 these are genuine hexagons, tending to the square. All three paired facets remain true along −t≤s≤t, so in dimension two the normal fan is constant. On each cone between adjacent normals a support is the same positive linear combination of its two facet widths. Hölder proves that the finite-facet midpoint body satisfies every full interpolated support constraint. The reverse inclusion uses the facet directions. Hence M_{1/2}=P_t(0). Put d=t+2cosh t−2. The endpoint areas are 4−d², and the midpoint area is 4−t². Therefore

\[
 \Delta_{1/2}=\log\frac{4-t^2}{4-(t+2\cosh t-2)^2}
             =\tfrac12t^3+O(t^4).
\]

The endpoints lie O(t) from the common square, itself an equality pair, giving the upper distance bound. In the plane every pair in 𝓔 is either homothetic or a pair of parallelograms. For a homothetic pair, the determinant of the two width vectors (h(e₁),h(e₂)) is zero. Our endpoint determinant is e^{−2t}−e^{2t}=−4t+O(t³). On bounded width vectors this determinant is Lipschitz. A pair within Hausdorff η of K_t,L_t must therefore have η≥c₁t if homothetic; far-away comparison pairs already satisfy this bound.

For the other case it suffices to bound distance from either hexagon H with widths a,b,c to every centered parallelogram. Here a,b→1, c→2 and d=a+b−c∼t. Every parallelogram sufficiently close to the square has its two pairs of edge normals close to the coordinate axes. This follows directly by taking limits of its bounded vertices: a full-dimensional limiting square has exactly those two edge directions. Consequently the three vectors v=(1,1/2), w=(1/2,1), v+w=(3/2,3/2) lie in one vertex normal cone of every such parallelogram Q, and

\[
 h_Q(v)+h_Q(w)-h_Q(v+w)=0.
\]

For H these supports are (a+c)/2, (b+c)/2 and 3c/2, respectively, so their difference is d/2. If d_H(H,Q)=η, support Lipschitz bounds give

\[
 d/2\le (\|v\|+\|w\|+\|v+w\|)\eta
       =(\sqrt5+3\sqrt2/2)\eta.
\]

Parallelograms outside the fixed square-neighborhood have distance bounded below independently of t and obey the same order bound for small t. Thus η≥c₂t in all cases. Taking the infimum over both types of equality pair proves (6.1). ∎

The construction uses distance to the **whole** equality class, not distance to a single optimizer or a fixed combinatorial type. It also has a fixed facet count and a common fan. Therefore a quadratic theorem cannot be salvaged merely by bounding the number of facets. A possible cubic exponent for the general compact class is a precise remaining question, not a conjecture claimed solved or a renamed equality assertion. The primary's qualitative compactness loses rates in local moment-coordinate bounds, boundary layers and spectral clustering of A; the degeneration in (6.1) shows that any quantitative replacement must also accommodate transitions between the homothety and product parts of the equality set.

## 7. Reproduction and evidence limits

The source directory contains the exact full brief; 141 frozen inputs including the complete I43 evidence; selected pinned blobs; fresh primary responses; current version records; source contracts and actually read passage extracts; corpus and literature search snapshots. All four shared status ledgers (`README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, `frontier/iterations/README.md`) are explicitly mutable. The task orchestration JSON is also mutable. Old seals are not refreshed. The unchanged I43 verifier reproduces successfully and separately reports its two known mutable ledger drifts.

Run from the project root:

```sh
python frontier/experiments/i44_logarithmic_equality_polytopes/check.py
python frontier/experiments/i44_logarithmic_equality_polytopes/verify.py
```

The diagnostics pass 200 exact assertions and check symbolic/rational identities for the audit, facet centroids, signed ridge forms, a nonsimple octahedron, finite exponential events, Gamma boundary moments, the matrix defect expansion, retained tensor completion and the cubic family. The verifier checks frozen/selected/response/passage hashes and sealed I44 artifacts, rehashes all 9,340 corpus files against the complete pinned tree, and reproduces both the new diagnostics and the old I43 verifier without writes. There are 31 successful retained responses, including four fresh matching pinned blobs, and 21 read-passage records. The original replay passes its 2,365 exact assertions and 125-artifact seal. These checks are reproducibility evidence, not mechanical proofs of the analytic limits or priority certification.

**Handoff:** original I43 partials PASS without repairs; current-primary symmetric E reduction is complete at the author-proof level presented in Section 5, attributed and awaiting independent parent proof review; unrestricted local K is not resolved; Proposition C, the hard scalar limit and Proposition Q are technical partials/obstructions. Do not promote them or the current-primary reduction to a seventh finding. The count remains 6/10. No shared ledgers were edited.
