# I46 — quantitative logarithmic stability: a planar power and the remaining dimensional gap

**Disposition: author-level proof of a uniform planar power estimate, with exponent 10, for arbitrary origin-symmetric convex bodies. The requested theorem in every fixed dimension remains unproved and unrefuted. No sharp cubic theorem, substantial-finding acceptance, or priority claim is made.** The planar result is a concrete positive partial, not merely fixed-facet Łojasiewicz or a lower-exponent obstruction. It needs a fresh independent proof review and an operation-level significance screen. In particular it uses classical planar operations as well as the accepted inequality; it should not be advertised as intrinsically enabled by a new all-dimensional OpenAI theorem. Under the brief's requirement that a technical restricted estimate does not count, this report does **not** nominate a seventh substantial finding.

Two different constructions were pursued. The unnormalized moment-square route pays a uniform soft approximation error and identifies a useful existing radius-only moment-Hessian estimate; the missing quantitative boundary/factor reconstruction is stated precisely. The geometric route replaces individual facet control by a reversible planar sine kernel and a three-region estimate, then reconstructs the endpoint equality pair. Every constant in that second route is independent of the number, angles, and minimum masses of facets. Approximation therefore passes the same exponent to all planar bodies.

The exact brief, subsequent dependency update, unchanged I43/I44 reports and briefs, and I45 review/parent verification are frozen in `../sources/i46_quantitative_logarithmic_stability/`. Only the three assigned I46 paths were written. No shared or prior edits, agents, staging, commits, or publication were used.

## 1. Target and premise boundary

For n≥2, 0<r<R and 0<τ<1/2, take full-dimensional origin-symmetric K,L with rB⊂K,L⊂RB and λ∈[τ,1−τ]. Define

\[
 P_t=\mathcal W[h_K^{1-t}h_L^t],\qquad
 \Delta_\lambda=\log|P_\lambda|-(1-\lambda)\log|K|-\lambda\log|L|.
\]

Let 𝓔 consist of all pairs (ΣK_j,Σc_jK_j) on complementary nonzero linear subspaces, with symmetric relative bodies K_j and c_j>0. Nonorthogonal subspaces and a single block are allowed. Put

\[
 d_{\mathcal E}(K,L)=\inf_{(K',L')\in\mathcal E}
 \max\{d_H(K,K'),d_H(L,L')\}.
\]

Comparison pairs have no imposed ball bounds. The full target is Δλ≥c(n,r,R,τ)d𝓔^α(n) with finite α(n), for all these pairs.

The pinned source is `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, family `The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026`. Its inequality, finite-slab concavity, moment coordinates, density, adjunctions and tensor/variance operations are accepted premises. Actual proofs in `introduction`, `reduction`, `moment`, `identities`, `density`, `tensor`, and `variance` were read. Twelve selected files are bound to the complete 13,223-entry/749-manuscript tree; the full ignored 9,340-file corpus is searched and rehashed.

At task start the full symmetric equality reduction E was conditional. The subsequent I45 update gives **E,C,B,Q PASS ORIGINAL WITHOUT REPAIRS**, with parent evidence reproduction. Its full review and parent record were read and frozen. Thus E can now be used as a proof-reviewed technical deduction, with full attribution to **Liu–Sun–Xiong, arXiv:2610.10152v2, 8 October 2026**, especially their tensor completion and boundary argument. Their external theorem was not assumed true. The nonsymmetric theorem is not audited or used. No part of I45's full audit is repeated here. The planar proof below does not require E at all: it explicitly constructs a pair in 𝓔.

I44/I45's hexagon Q gives d𝓔≍t and Δ1/2=½t³+O(t⁴). The formulas needed here were checked symbolically again, but the whole distance audit is not duplicated. Hence an exponent below 3 cannot hold on any ball-bounded class containing that family. It does not assert sharpness of a cubic positive bound. Our exponent 10 is consistent with it.

## 2. Early primary-source scope screen

The actual primary statements and relevant proofs, not search snippets, were used. Fresh official records confirm the specified versions; retrieval bytes, hashes and failures are retained. This is a bounded search, not worldwide-priority certification.

* [Böröczky–De v6](https://arxiv.org/abs/2101.02549v6), Theorems 1.4–1.5 and the constructive proof in §§4–6: under n common linear reflections, multiplicative factor reconstruction has error O((ε/τ)^(1/(95n))). Its coordinate-product inclusion, spectral grouping and Prékopa–Leindler input use those symmetries. This is already a positive power theorem, not the unrestricted target. Their cut-box example also warns that dimension changes sharp powers.
* [Lu v3](https://arxiv.org/abs/2608.20730v3), Theorems 1.2, 1.4, 1.6 and the fiber/equality proofs: qualitative E with n−2 common orthogonal reflections and the revolution variants. The planar case has no extra reflection hypothesis, but these results do not state a uniform quantitative remainder.
* [Xi v4](https://arxiv.org/abs/2307.04266v4), §3 and §4: the planar support reconstruction/Hölder argument, and global zonoid equality against arbitrary symmetric comparisons. Its exact relation lemma and van Handel's nonsmooth mixed-area identity are essential antecedents; neither is credited to I46. In particular planar equality and zonoid global equality are not new targets.
* [Van Handel, final author version](https://web.math.princeton.edu/~rvan/logzon221121.pdf), Lemma 3.6, Remark 3.4 and §4: the planar generating measure, the spectral/Bochner mechanism, and nonsmooth local equality. Our inverse Markov formulation is a planar rewriting of existing mixed-area structure; the quantitative three-region and endpoint argument below is the step requiring significance scrutiny.
* [Wang v2](https://arxiv.org/abs/2510.19061v2) and [He–Liu v1](https://arxiv.org/abs/2510.21530v1): smooth conditional rigidity/density results. No unrestricted ball-bounded finite power is extracted from their smooth hypotheses.
* The titles of [Colesanti–Livshyts–Marsiglietti](https://arxiv.org/abs/1606.06586) and [Colesanti–Livshyts](https://arxiv.org/abs/1710.10708) contain “stability” or “quantitative”, but their actual main statements concern validity/rigidity near a ball in a smooth topology. They are not a Δ-versus-distance power estimate for all planar bodies. The latter authors explicitly place their main result within Kolesnikov–Milman's local theory.
* [Xi's September 2026 note](https://arxiv.org/abs/2609.08495), Theorem 1.1 and all three proof steps, supplies a stronger planar inequality through relative Bonnesen radii and mixed area. It does not state the target stability rate. Its operations are nevertheless a serious alternative source for an eventual technical reduction of our planar result; absence of a printed rate is not proof of substantiality.
* [Klartag, *Logarithmically-concave moment measures I*](https://www.math.tau.ac.il/~klartagb/papers/lc_moment.pdf), Theorem 1 and pp. 24–25: for the moment potential of a log-concave density on a bounded convex K, **Δφ≤2R(K)²**, with no smoothness of ∂K required. The proof first uses the diffusion covariance estimate and then removes the smooth/strictly convex target assumptions. This pays a uniform Hessian cap for the hard Gaussian-truncated target in §3; claiming that only the diverging 4/ε bound is available would be incorrect.

The BLYZ planar equality/minimization proof, the current LSX limiting mechanism, and the pinned companions were also inspected. No direct unrestricted planar Δ≥cd𝓔^10 statement was found in this bounded screen. This is not a novelty verdict. A mislabelled search lead downloaded as `local-quant-fresh.pdf` is actually Kolesnikov–Livshyts' local/seminorm paper; its true title is recorded. The failed author-site CLM request is retained, followed by a successful arXiv retrieval. Neither is silently treated as the requested successful source.

## 3. Construction A: quantitative unnormalized squares

### 3.1 Approximation error with explicit complexity dependence

For a finite spanning list, let P(t) be its hard slab body between common balls and

\[
 U_q(x,t)=\sum_{i=1}^N|p_i\cdot x/h_i(t)|^q,\quad
 B_q(t)=\{U_q\le1\},\quad Z_{q,\epsilon}(t)=\int e^{-U_q-\epsilon|x|^2/2}dx.
\]

All p_i are unit here; even q≥2. Homogeneity gives the exact identity

\[
 N^{-1/q}P(t)\subset B_q(t)\subset P(t),\qquad
 Z_{q,0}(t)=\Gamma(1+n/q)|B_q(t)|.                 \tag{3.1}
\]

Indeed integrate the layer sets of e^(−U_q); their volumes are s^(n/q)|B_q|. The same radial computation gives

\[
 E_{q,0}|x|^2
 =\frac{\Gamma(1+(n+2)/q)}{\Gamma(1+n/q)}
   \frac{\int_{B_q}|x|^2dx}{|B_q|}\le C_nR^2.
\]

Jensen applied to exp(−ε|x|²/2) and the upper bound by 1 therefore give, uniformly in t,

\[
 |\log Z_{q,\epsilon}(t)-\log|P(t)||
 \le C(n,R)\epsilon+C_n(1+\log N)/q.              \tag{3.2}
\]

This estimate is for the full finite hard body, without minimum facet mass. Redundant directions are allowed. A spherical a-net has N≤C_na^(−(n−1)); since support bounds are uniformly Lipschitz, its outer Wulff error is O(a) under fixed r,R. Thus a finite approximation can be chosen with error e and only logarithmic N dependence in (3.2).

Let δ=Δλ>0. Choose the direction error e≤δ, ε=δ, and q≥C(1+log N)/δ. Concavity and interior secants then select a time in [1/3,2/3] with unnormalized curvature defect D≤Cδ. This uses the same Green/selection operation as I44/I45 but does not require equality. The exact completed-square identity, with β_i=−qb_i and dense test error at most δ, yields

\[
 T(v)\le C\delta,\quad E\mathscr D(P)\le C\delta,
 \quad E|W|^2\le C.                              \tag{3.3}
\]

All constants so far depend only on n,r,R,τ. The density operation chooses each compact test separately; no inverse norm has been smuggled into (3.3). The Gaussian term is retained. At a nonzero normalized chord slope, the mean score need not tend to zero; it must be retained in the flux equation below.

### 3.2 Hard moment coordinates do have quantitative interior bounds

For any symmetric C between rB and RB and 0≤ε≤1, consider

\[
 d\mu_{C,\epsilon}=Z^{-1}1_Ce^{-\epsilon|x|^2/2}dx,
 \quad (\nabla\varphi)_\#(e^{-\varphi}dz)=\mu_{C,\epsilon},
 \quad \nabla\varphi(0)=0.
\]

The compact-target moment theorem and Klartag's Theorem 1 apply to the smooth positive target density on int C, even if ∂C is nonsmooth. With τ=D²φ,

\[
 \tau\le2R^2I,\quad |\nabla\varphi|\le R,
 \quad c|z|-C\le\varphi(z)\le C+R|z|.             \tag{3.4}
\]

Here c,C>0 depend only on n,r,R. For completeness, the lower linear growth follows by integrating the two symmetric supporting planes, exactly as in the pinned moment proof:
φ(z)−φ(0)≥∫|x·z|dμ−n≥c|z|−n. The identity E[z·∇φ]=n follows from expanding cutoffs; a preliminary coercive bound follows from the gradient image containing a ball. The density on rB has a uniform positive lower bound. The upper growth follows from |∇φ|≤R. Normalization ∫e^(−φ)=1 bounds φ(0) on both sides using these two bounds.

The moment equation is detτ=Z exp(−φ+ε|∇φ|²/2). Consequently on B_L,

\[
 c e^{-RL}I\le\tau\le2R^2I,\qquad
 e^{-\varphi}\ge c e^{-RL},\qquad
 \nu(B_L^c)\le C(1+L)^{n-1}e^{-cL}.              \tag{3.5}
\]

The lower Hessian estimate uses the determinant lower bound divided by (2R²)^(n−1), not an unsupported ellipticity assertion. These are quantitative bounds for the **hard target's** moment potential; the cap is not asserted uniformly for all finite-q soft targets. I45's local convergence allows passage to this hard potential on each fixed core after q increases, but that must precede using (3.5).

If hard-limit fields retaining (3.3) have been constructed, (3.5) implies the explicit core estimate

\[
 \int_{B_L}|D_zP|^2dz\le C e^{2RL}\delta.         \tag{3.6}
\]

On B₁, Poincaré and W=P∇φ−div P give a bounded mean matrix A and ||P−A||₂+||W−A∇φ||₂≤C√δ. Nondegeneracy is uniform: (3.5) on B₁ implies ∇φ is uniformly strongly monotone there, so ∫_{B₁}∇φ∇φᵀ is uniformly positive. On larger balls, comparison of averages gives

\[
 \|P-A\|_{L^2(B_L)}+\|W-A\nabla\varphi\|_{L^2(B_L)}
 \le C(1+L)^{n/2+1}e^{RL}\sqrt\delta.           \tag{3.7}
\]

This is a conditional field estimate, not a claim here that the necessary finite-defect hard-limit field construction has already been completed. For ε>0 the hard density is not uniform, so its Gaussian divergence term must also be retained.

The exact symmetry Pτ=τPᵀ then bounds Aτ−τAᵀ on each core by the right side of (3.7). Averaging τ on B₁ supplies a uniformly conditioned positive matrix H; symmetrizing H^(−1/2)AH^(1/2) changes it by O(√δ). In that constant frame, merge consecutive eigenvalues separated by less than γ. There are at most n clusters, each diameter at most nγ. Between different clusters, the commutator estimate bounds the corresponding mixed Hessian blocks by Cγ^(−1) times the error in (3.7). These are actual elementary matrix estimates; their dependence on L and γ is explicit.

A Euclidean boundary layer also has a uniform estimate:

\[
 |C\setminus\{x:\operatorname{dist}(x,\partial C)\ge a\}|/|C|
 \le1-(1-a/r)^n\le na/r.                          \tag{3.8}
\]

Indeed (1−a/r)C+aB⊂C. With the L² bound on W, its contribution to a smooth flux test is O(√a)||∇g||∞. This part does not require facet regularity.

### 3.3 What is still unpaid in this route

These estimates improve the rate budget, but they do not complete the chain. At finite deficit one needs to construct the hard-limit fields with their normal distribution, then turn small mixed Hessian blocks on B_L into a **single nearby product body and compatible endpoint factor dilations**, quantitatively. For L proportional to log(1/δ), (3.5)–(3.7) give power budgets, but do not by themselves identify the product factors or transfer them to K,L.

In particular the boundary relation has an error tested against g(x), not against arbitrary functions of the normal. Its exact limiting form before ε↓0 is

\[
 \int_C W\cdot\nabla g\,d\mu_{C,\epsilon}
 =-Z^{-1}\int_{\partial C}g\,b(\nu)h_C(\nu)e^{-\epsilon|x|^2/2}dS
   -(EF)\int_Cg\,d\mu_{C,\epsilon}.               \tag{3.9}
\]

For W=Ax, integration by parts contributes −trA+εx·Ax in the bulk. Dropping the centering or Gaussian term would be wrong. Approximate (3.9) in a position-test norm does not immediately control b(ν) in the cone-volume norm on a nonsmooth boundary: the normal map is not uniformly Lipschitz. Almost commuting matrices at one point also do not make an entire gradient image a product. I have not proved a uniform normal-test conversion plus factor/endpoint reconstruction with a paid power. Neither estimate is declared a lemma or inferred from qualitative E. No conclusion about impossibility of any finite power follows.

## 4. Construction B: a facet-independent planar power

**Theorem P10 (author proof, not independently reviewed).** In dimension two, for every 0<r<R and 0<τ<1/2 there is c(r,R,τ)>0 such that

\[
 \boxed{\quad\Delta_\lambda(K,L)\ge c(r,R,\tau)
              d_{\mathcal E}(K,L)^{10}.\quad}             \tag{4.1}
\]

This holds for all symmetric convex bodies between the indicated balls and all λ∈[τ,1−τ]. No extra reflection, smoothness, common fan or facet-count hypothesis is imposed. The constructed comparison pair is either homothetic or consists of parallelograms with common edge directions, including oblique ones.

The proof below is included in full. Known support reconstruction and mixed-area facts are credited; the facet-independent quantitative estimate is not replaced by a compactness lemma.

### 4.1 Elementary mixed-area and cap estimates

Write the mixed area as V(A,B), so |A+tB|=|A|+2tV(A,B)+t²|B|. For symmetric A with rB₂⊂A⊂RB₂ and any symmetric B, let a=V(A,B)/|A|. Then

\[
 d_H(B,aA)^2\le C(r,R)\{V(A,B)^2/|A|-|B|\}.       \tag{4.2}
\]

Here is a proof suitable also for polygons. Even support functions are π-periodic H¹ functions. Their area form is
V(f,g)=½∫₀^{2π}(fg−f′g′). Expand h_A=a₀+u and e=h_B−ah_A=b₀+v into constant and nonconstant even Fourier modes. With

\[
 \|u\|_*^2=\frac\pi2\sum_{k\ge1}(4k^2-1)(a_k^2+b_k^2),
\]

one has |A|=πa₀²−||u||_*² and V(h_A,e)=πa₀b₀−〈u,v〉_*=0. Thus

\[
 -V(e,e)=\|v\|_*^2-\pi b_0^2
 \ge\frac{|A|}{\pi a_0^2}\|v\|_*^2
 \ge(r/R)^2\|v\|_*^2.
\]

Also |b₀|≤C||v||_*. Cauchy–Schwarz and Σ(4k²−1)^(−1)<∞ give ||v||∞≤C||v||_*. Finally −V(e,e)=V(A,B)²/|A|−|B| and d_H=||e||∞. This proves (4.2), including its uniform constants. The same computation says that the mixed-area quadratic form is strictly negative on the V-orthogonal complement of any positive-area symmetric support function. It extends to differences of support functions; no positivity of e is needed.

We also use the following elementary inclusion estimate. If rB₂⊂A⊂B⊂R₁B₂, then

\[
 d_H(A,B)\le C(r,R_1)\sqrt{|B|-|A|}.              \tag{4.3}
\]

Choose a direction with support excess η and an exposed point x of B at that height. The convex hull of x and the radius-r segment through zero perpendicular to that direction lies in B. Its portion above the supporting line of A is a triangle of area at least c(r,R₁)η²: at depths between η/2 and η below x the section length is at least rη/R₁. It lies outside A. This proves (4.3) without regularity assumptions.

### 4.2 The planar reversible kernel and the curvature remainder

First consider polygons and a time interval on which all current true facets are fixed. Work on the projective circle 𝕋=R/(πZ), with one point per antipodal normal pair. Let s_i>0 be the **sum** of the two edge lengths, h_i the support, and V the area. The planar curvature reconstruction formula is

\[
 h(u)=\frac14\sum_j|\sin(u-u_j)|s_j,\qquad
 V=\frac12\sum_i h_is_i.                          \tag{4.4}
\]

It follows either from the planar segment representation or from (d²/dθ²+1)|sinθ|=2Σ_{k∈Z}δ_{kπ}, remembering the paired mass. It holds for signed variations as well; the π-periodic kernel of d²/dθ²+1 is zero. Define

\[
 \nu_i=\frac{h_is_i}{2V},\quad
 T_{ij}=\frac{|\sin(u_i-u_j)|s_j}{4h_i},\quad
 \pi_{ij}=\nu_iT_{ij}=\frac{s_is_j|\sin(u_i-u_j)|}{8V}.      \tag{4.5}
\]

T is stochastic, reversible for ν, and invertible. Invertibility follows directly from the invertibility of the curvature reconstruction on the finite support: if all reconstructed facet supports vanish, the piecewise sinusoidal interpolant between consecutive normals is zero, hence so is its curvature measure. Consecutive true normals have projective gaps strictly below π. T preserves the ν-mean-zero subspace.

On that subspace all eigenvalues of T lie in [−1,0). The lower bound −1 follows from its Markov L² contraction. For strict negativity let y have ν-mean zero and let g be the signed support variation with curvature masses s_i y_i. Then g(u_i)/h_i=(Ty)_i,
V(h,g)=V〈1,Ty〉ν=0, and V(g,g)=V〈y,Ty〉ν. The strict negative mixed-area statement from (4.2)'s proof gives negativity unless y=0. This argument also proves the spectral assertions without relying on a smooth Hilbert–Brunn–Minkowski operator.

On an exponential facet path h_i(t)=a_i exp(b_i t), put f_i=b_i, c=〈f〉ν, q=f−c and y_i=s_i′/s_i. Differentiating (4.4) gives f=Ty. Differentiating area gives V′/V=2c and

\[
 \frac{V''}{V}=2\langle f,f\rangle_\nu+2\langle f,y\rangle_\nu.
\]

Therefore its log curvature D=−(log V)″ is

\[
 D=2\langle q,(-T^{-1}-I)q\rangle_\nu
 \ge2\langle q,(I+T)q\rangle_\nu
 =\sum_{i,j}\pi_{ij}(q_i+q_j)^2.                 \tag{4.6}
\]

For an eigenvalue −a, 0<a≤1, the inequality is 1/a−1≥1−a. The last expression is a nonnegative **sum** form, not the signed ridge expression from I44. It uses the inverse of the global planar reconstruction operator, so the negative individual ridge coefficients do not contradict it. For two directions, T exchanges them and the nonconstant mode is −1, exactly permitting independent side dilations.

### 4.3 A quantitative three-region dichotomy

Let σ=Σs_iδ_{u_i}/M, M=Σs_i be the perimeter probability. For rB₂⊂P⊂RB₂, M is between 2πr and 2πR, and ν and σ have uniformly comparable densities. Also

\[
 \int|\sin(u-v)|d\sigma(v)=4h(u)/M\ge\kappa>0,
 \qquad\kappa=2r/(\pi R).                         \tag{4.7}
\]

For any 0<s<s₀(r,R), and any real function q on the normals, set

\[
 \mathcal J(q)=\iint|\sin(u-v)|(q(u)+q(v))^2d\sigma(u)d\sigma(v).
\]

There is the following dichotomy, with constants depending only on r,R:

1. There are two actual normal directions a,b separated by a fixed positive angle such that σ lies outside the two projective 4s-neighborhoods with mass at most s. In this case the enclosing parallelogram
   Q={x:|a·x|≤h_P(a), |b·x|≤h_P(b)} satisfies P⊂Q and d_H(P,Q)≤Cs.
2. One has ||q||²_{L²(ν)}≤Cs^(−4)𝒥(q).

Here is the full construction. Partition the projective circle into O(1/s) arcs of diameter at most s/10. One arc A₁ has mass m₁≥cs; choose a from its support. By (4.7), the set at projective angular distance at least κ/2 from a has σ-mass at least κ/2 (use |sin|≤distance on the complement and ≤1 everywhere). Some arc intersected with this set has mass m₂≥cs; call the restricted set A₂ and choose b in its support. The angle between a and b, and all points in A₁ and A₂, is bounded below independently of s.

If the mass outside the 4s-neighborhoods of a,b exceeds s, partition that remaining set by the same arcs. One resulting set A₃ has mass m₃≥cs². Its points have angular separation at least 3s from A₁ and A₂; thus all corresponding sine kernels are at least cs, while the A₁–A₂ kernel is bounded below by a constant. All sets are disjoint. If Q_i=m_i^(−1)∫_{A_i}q²dσ, integrate

\[
 4q(u)^2\le3\{(q(u)+q(v))^2+(q(u)+q(w))^2+(q(v)+q(w))^2\}
\]

over A₁×A₂×A₃, and likewise with the roles permuted. Each normalized edge integral is bounded by 𝒥 divided by its sine lower bound and its two masses. The worst denominator is cs·cs·cs²=cs⁴. Hence Q_i≤Cs^(−4)𝒥 for all i. For any u on the circle, at least one of the kernels to **all** of A₁ or all of A₂ is bounded below by a positive constant, since a,b are uniformly separated and the arcs are small. On that set use q(u)²≤2(q(u)+q(v))²+2q(v)² and average over the chosen arc. Integrating u gives
||q||²_{L²(σ)}≤C𝒥/min(m₁,m₂)+C(Q₁+Q₂)≤Cs^(−4)𝒥. Comparability gives alternative 2.

If the outside mass is at most s, move all σ-mass in the two neighborhoods to a,b, and move the exceptional mass to a. The 1-Lipschitz sine kernel in (4.4) shows that the resulting two-segment support h₀ satisfies ||h_P−h₀||∞≤Cs. For s small, h₀≥r/2, so it is a full-dimensional parallelogram with normals a,b. At a,b its supports differ from h_P by at most Cs. The uniformly invertible two-normal coordinate map shows that replacing these two widths by h_P(a),h_P(b) changes its vertices, and hence its support function, by at most Cs. This proves alternative 1 with the stated **actual** active directions, not the normals of an arbitrary fitted parallelogram.

No individual facet has been selected with a lower mass bound. The lower bounds are for arcs containing potentially arbitrarily many facets. This is the step that survives unbounded complexity.

### 4.4 Selecting one time and reconstructing both endpoints

Let δ=Δλ(K,L)>0 for polygons. The full interpolation has a finite slab description using the union of the endpoint normal directions. Indeed, between consecutive directions in that union each endpoint support is a positive linear combination of its endpoint values. Hölder says that satisfying the interpolated endpoint constraints implies the full intermediate-direction constraint. The reverse inclusion is immediate. Some listed constraints may be redundant at intermediate times; only **true** facets are used in §§4.2–4.3.

There are finitely many exceptional times for the active list: each candidate vertex/constraint event is a finite real exponential sum, hence is either identically zero or has finitely many zeros (divide by the least exponential and use Rolle inductively). In the plane a genuine vertex has exactly two true incident edges. Thus the log-volume curve is smooth on the complementary open intervals, and (4.6) applies there. Possible singular curvature at exceptional times is nonnegative by concavity and causes no difficulty in the following bound.

Put g(t)=log|P_t|−(1−t)log|K|−t log|L|. Concavity, g(0)=g(1)=0 and g(λ)=δ give 0≤g≤δ/τ. At differentiability times in [1/4,3/4], |g′|≤4δ/τ. The Green identity for the nonnegative curvature measure gives

\[
 \int_{1/3}^{2/3}D(t)dt\le C_\tau\delta.
\]

Its kernel Gλ(t)=min{(1−λ)t,λ(1−t)} is bounded below there by τ/3. Consequently select a nonexceptional t∈[1/3,2/3] with D≤Cτδ. Write P=P_t, c=〈b〉ν and v=Varν(b). All supports and b=log(h_L/h_K) on the current facets are uniformly bounded in terms of r,R. The same chosen time satisfies

\[
 2c=\log|L|-\log|K|+g'(t),\quad
 \log(|K|/|P|)+2tc=-g(t)+tg'(t)=O_\tau(\delta).       \tag{4.8}
\]

If alternative 2 of §4.3 occurs, (4.5)–(4.6) give v≤Cδs^(−4). On each true facet h_K=h_P exp(−tb), so

\[
 V(P,K)/|P|=E_\nu e^{-tb}
 =e^{-tc}E_\nu e^{-t(b-c)}\le e^{-tc}(1+Cv).          \tag{4.9}
\]

The last inequality is Taylor's formula on a fixed bounded interval, with the linear term averaging to zero. Combining (4.8) and (4.9), and the corresponding formulas for L, bounds each mixed-area defect in (4.2) by C(v+δ). Thus for a_K=V(P,K)/|P| and a_L=V(P,L)/|P|,

\[
 \max\{d_H(K,a_KP),d_H(L,a_LP)\}
 \le C\sqrt{\delta+\delta s^{-4}}.                 \tag{4.10}
\]

The pair (a_KP,a_LP) belongs to the one-block part of 𝓔. Both coefficients are positive and uniformly bounded because they average h_K/h_P or h_L/h_P against ν.

If alternative 1 occurs, use its actual active normals a,b and form

\[
 Q_0=\{|a\cdot x|\le h_K(a),\ |b\cdot x|\le h_K(b)\},
 \quad Q_1=\{|a\cdot x|\le h_L(a),\ |b\cdot x|\le h_L(b)\}.
\]

These contain K,L. Their logarithmic two-width interpolation at time t is exactly Q from alternative 1, since a,b are active at that time. Their areas satisfy log|Q|=(1−t)log|Q₀|+t log|Q₁|. The angle bound gives common outer ball bounds for Q₀,Q₁. Moreover P⊂Q and d_H(P,Q)≤Cs imply log(|Q|/|P|)≤Cs, by P+sCB⊂(1+Cs/r)P. Therefore

\[
 (1-t)\log\frac{|Q_0|}{|K|}+t\log\frac{|Q_1|}{|L|}
 =g(t)+\log\frac{|Q|}{|P|}\le C(\delta+s).          \tag{4.11}
\]

Both summands are nonnegative and t is bounded away from the endpoints. Each area excess is at most C(δ+s), and (4.3) gives

\[
 \max\{d_H(K,Q_0),d_H(L,Q_1)\}\le C\sqrt{\delta+s}.       \tag{4.12}
\]

The pair (Q₀,Q₁) is in 𝓔: in the invertible (a·x,b·x) coordinates it is two rectangles, with independently dilated interval factors. Undoing that map gives complementary, possibly nonorthogonal, edge subspaces.

Set s=δ^(1/5) for sufficiently small δ. Both (4.10) and (4.12) are bounded by Cδ^(1/10). This proves (4.1) for polygons. For δ above the fixed small threshold use the bounded distance to, for example, the equality pair (rB₂,rB₂), and decrease c. If δ=0, apply the same argument with every auxiliary positive upper bound on δ and let it tend to zero; it gives d𝓔=0, which suffices for (4.1) without assuming that 𝓔 is closed.

### 4.5 Passing to arbitrary bodies

Approximate symmetric K,L by symmetric polygons in Hausdorff distance. All approximants lie between (r/2)B₂ and (2R)B₂ once sufficiently close. The constant and exponent just proved are independent of their normal configurations and counts. Uniform convergence of positive supports gives uniform convergence of their logarithmic bounds. If two positive bounds differ multiplicatively by e^(±η), their Wulff bodies lie between the same dilates; hence their areas and deficits converge. Finally distance to any subset of a metric space is 1-Lipschitz, so d𝓔 converges as well. Passing to the limit proves Theorem P10. No Łojasiewicz exponent depending on the approximant is used. ∎

## 5. Why this does not yet finish the full task

The planar sine reconstruction is linear in the surface-area measure and every symmetric planar body is a zonoid. In n≥3 the surface-area map is nonlinear, general symmetric bodies need not be zonoids, and the inverse used in (4.6) is not replaced by a stochastic kernel with this three-point geometry. The already-known zonoid equality induction does not automatically give a uniform quantitative estimate for arbitrary bodies. Lu's fiber argument would require quantitative synchronization and near-product control of varying fibers; inserting P10 does not pay those interfaces. Neither an all-dimensional exponent nor an extension to n−2-reflection bodies is claimed.

For a separate fixed-facet semialgebraic approach, a fixed normal configuration and a fixed rational λ may yield a Łojasiewicz inequality after encoding vertices and volume. Its exponent depends on the number of variables, hence on facets. For variable irrational λ the raw power expressions are not even semialgebraic; one needs a different definability argument or first reduces the parameter. A net approximation with N growing as a negative power of its error does not make an N-dependent exponent uniform: even a lower bound of the schematic form c_N d^{N} disappears faster than any fixed power as N increases. The O(a) approximation error may then exceed the purported positive remainder. No such limit is used in P10 and no fixed-N result is presented as a solution.

The Q family excludes α<3 in dimension two. The planar P10 proof provides the interval 3≤α_opt≤10 for any fixed class sufficiently broad to contain Q, **if α_opt denotes the infimum of admissible exponents for that class**. It does not determine α_opt; for narrower r,R classes Q might not fit and that lower bound need not apply. No cubic-in-all-dimensions assertion is made. No family with superpolynomially small deficit at a fixed distance from the entire equality class was constructed.

## 6. Validation, evidence freeze, and handoff

The exact diagnostic reconstructs actual planar zonotopes from rational unit normals and positive paired curvature masses. It checks stochasticity/reversibility, the signed mixed-area signature, the inverse-kernel/log-Hessian identity, positive semidefiniteness of the retained sum form and its difference from curvature, and all ternary slopes in sixteen configurations. It also checks the triangle identity, the cubic-family expansion and the rate balance. It passes **3,319 exact assertions**. These are meaningful finite tests of signs, factors and degeneracies; they are not a proof of the universal clustering argument or the analytic limits.

Two preparation failures are preserved in `execution-notes.json`: the initial interpreter lacked SymPy, so the existing pinned local wheels were copied into the owned I46 evidence directory; an initial test list accidentally contained antipodal representatives of the same projective direction, making reconstruction singular. The final diagnostic uses distinct projective directions and verifies invertibility. This was a fixture correction, not deletion of a counterexample under the theorem's hypotheses. The failed CLM response and the mislabelled local-paper lead remain in the source ledger. No prior artifact or seal was altered.

Run from the repository root:

```sh
python frontier/experiments/i46_quantitative_logarithmic_stability/check.py
python frontier/experiments/i46_quantitative_logarithmic_stability/verify.py
```

The verifier is read-only and disables bytecode. It checks the exact sealed artifact set, frozen inputs, all selected Git blobs, current responses, logged passage extracts, and all 9,340 corpus files against the full pinned tree. It checks the unchanged I43/I44/I45 sealed artifact identities; it does not rerun their full analytic audits. All four live shared ledgers and the task orchestration record are explicitly mutable, and later drift is reported separately. The I45 dependency update is a later frozen input, not a refreshed earlier seal. Source identity and exact arithmetic are not mathematical acceptance or literature priority certification.

**Handoff:** P10 is a complete author-proof planar positive partial with facet-independent constants and explicit comparison pairs. Its independent analytic review and significance remain open; it is not an accepted seventh finding. Construction A has explicit approximation and hard moment-coordinate budgets, but still lacks quantitative hard-field/normal-test/factor reconstruction. The full all-dimensional finite-power target is unproved and unrefuted. E and Q retain I45's attributed proof-review status, without importing the unaudited centered nonsymmetric claim.
