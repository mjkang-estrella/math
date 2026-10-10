# I48 — independent operation-level significance review of planar P10

**Contribution verdict: TECHNICAL ONLY, conditional on the separate original-proof audit. Not EXACT DUPLICATE.** I found no source printing P10 with precisely its distance, quantifiers and exponent. That is not the reason for this verdict. The combination of the classical planar mixed-area operator, the weighted dual Cheeger inequality of Bauer–Jost, and elementary support/area reconstruction supplies the disputed uniform cluster-to-endpoint bridge. Section 3 proves the reduction explicitly, including the mass outside the bipartition and the choice of actual active normals. It gives the stronger intermediate bound

\[
 d_{\mathcal E}(K,L)\le C(r,R,\tau)\Delta_\lambda(K,L)^{1/6},
\]

which implies the requested exponent 10 on this bounded class. This is a reduction certificate for the significance screen, **not a separately nominated finding or an independent PASS for I46's original argument**. No I47 completed review was read or used; I did not poll its task. The parent retains responsibility for original-proof acceptance and disposition. I noticed no specific counterexample or original P10 proof gap in this screen.

The breadth of P10 is real: arbitrary symmetric planar bodies, unbounded facet complexity, no minimum facet mass, no common reflections, and distance to the entire equality class. Those features must be preserved in a demotion. The proof below preserves them. The mathematical work in I46 is useful, but the three-region bookkeeping can be replaced by an already available quantitative graph operation followed by explicit elementary interfaces. It therefore does not meet this project's requirement of a new substantive bridge enabled by the pinned OpenAI proofs. In particular, its planar concavity input was already classical. The higher-dimensional finite-power problem remains unpaid; neither this review nor the improved intermediate rate resolves it.

## 1. Scope and premise boundary

Fix **every** (0<r<R), (0<\tau<1/2). The bodies (K,L\subset\mathbb R^2) are arbitrary full-dimensional origin-symmetric convex bodies with (rB\subset K,L\subset RB), and (\lambda\in[\tau,1-\tau]). Put

\[
 P_t=\mathcal W[h_K^{1-t}h_L^t],\qquad
 \delta=\Delta_\lambda=\log|P_\lambda|-(1-\lambda)\log|K|-\lambda\log|L|.
\]

The planar class (\mathcal E) is the union of all homothetic symmetric-body pairs and all pairs of centered parallelograms with common side directions, including oblique directions. Its comparison bodies are not required to obey the original ball bounds. We use the maximum of the two Hausdorff distances and take the infimum over this whole class. Neither fixing the directions of the comparison parallelograms nor deleting the homothetic branch would answer the brief.

All pinned results **and proof operations** at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` remain accepted premises. The full inventory has 13,223 entries and 749 manuscripts, and the ignored corpus has 9,340 files. The actual logarithmic manuscript's introduction, reduction, tensor and variance proofs were read, not merely its catalogue description. Its finite-slab concavity and soft limits are available; they are not an automatic quantitative factor-reconstruction theorem. The planar reduction below does not need its new tensor mechanism.

The full I46 report and original brief, relevant I43/I44 results and I45 audit, the I45 dependency update, parent evidence checks, and the project finding/history ledgers are frozen. I45 gives E,C,B,Q PASS ORIGINAL WITHOUT REPAIRS. Symmetric E is the attributed Liu–Sun–Xiong specialization, not a new project discovery. P10 and the reduction here need neither E nor the external centered theorem. Q excludes exponents below three only on ball-bounded classes containing that family. It is not a positive cubic estimate.

I43's collapsing-gap hexagons correctly prevent a uniform coercivity bound modulo only dilation. I44's normalized soft defect vanishes at leading order for every slope; it cannot provide the missing quantitative rigidity. The present graph argument uses the **unnormalized hard planar curvature** and the whole equality class. It does not revive either failed route.

The original objective is ten **substantial, newly upstream-enabled** findings; the history records six accepted findings and excludes standard transfers. This review does not silently replace that gate by “a theorem whose statement was not found online,” nor by “a better printed exponent.” No acceptance, count change, MathDB score or worldwide priority claim is made.

## 2. Actual primary-source comparison

Fresh primary downloads and searches were initiated before developing the reduction. Response bodies, dates, versions, failures, proof passages and source contracts are retained. The following are proof-level comparisons, not conclusions from titles.

### 2.1 Classical and zonoid antecedents

**Böröczky–Lutwak–Yang–Zhang**, *The log-Brunn–Minkowski inequality*, [author PDF](https://math.nyu.edu/~yangd/papers/LBMI.pdf), Theorems 1.3–1.4, already gives the unrestricted symmetric planar inequality and exactly the two equality branches. Theorem 4.1 retains the relative Bonnesen quadratic

\[
 |K|-2tV(K,L)+t^2|L|\le0\quad(r(K,L)\le t\le R(K,L)).
\]

Its proof uses inner parallel bodies, mixed-area monotonicity and integration. Equality at an endpoint reconstructs a dilate plus a segment. Lemma 5.1 integrates this quadratic against the surface-area measure, then reduces equality of support ratios to two extreme values; Theorem 5.2 identifies equal planar cone-volume measures. These are genuine geometric operations, not just qualitative statements to be ignored. They do not themselves state P10.

**Xi**, [arXiv:2307.04266v4](https://arxiv.org/abs/2307.04266v4), §3, writes the planar support as an integral of a sine/cosine kernel against the curvature measure and applies Hölder. The equality argument says either the measure has two antipodal pairs of directions or the density ratio is constant. In §4, Theorem 4.4 allows a zonoid base and **arbitrary symmetric comparison body**. Its projection Hölder equality and relation lemma synchronize direct summands. It is incorrect to dismiss this as only a smooth or local result. Conversely, quantitative continuity of the reverse-to-forward variational minimizer and quantitative synchronization do not follow merely from its equality theorem. Our reduction uses its linear planar reconstruction operation, without asserting that “every planar body is a zonoid” alone pays stability.

**Van Handel**, *The local logarithmic Brunn–Minkowski inequality for zonoids*, [final author version `logzon221121.pdf`](https://web.math.princeton.edu/~rvan/logzon221121.pdf), Lemma 3.6 proves the planar Bochner bound by Cauchy–Schwarz and the explicit generating measure. Remark 3.4 displays the retained square rather than merely an inequality. Section 4, especially Lemmas 4.2–4.3, replaces the smooth eigenfunction equation by a nonsmooth mixed-area-measure identity; it is a real nonsmooth equality argument. The finite inverse sine operator below is a conjugate of this classical planar mixed-area structure. Rewriting it as a reversible Markov matrix is not, by itself, a new coercivity mechanism. The additional quantitative input used here is an existing graph theorem.

### 2.2 The graph theorem actually needed

**Bauer–Jost**, [arXiv:0910.3118v4](https://arxiv.org/abs/0910.3118v4), *Bipartite and neighborhood graphs and the spectrum of the normalized graph Laplace operator*, §2, equation (29), and **Theorem 3.2 with its proof**, applies to finite, connected, undirected **weighted** graphs. Loops are allowed, not required. Its normalized Laplacian is (I-T). For

\[
 \bar h=\max_{A\cap B=\varnothing,\ A,B\ne\varnothing}
 \frac{2w(A,B)}{\nu(A\cup B)},\qquad \beta=1-\bar h,
\]

it proves

\[
 2\bar h\le\lambda_{\max}(I-T)
 \le1+\sqrt{1-\beta^2}.
 \tag{2.1}
\]

The proof passes from the sum form (rac12\sum w_{ij}(f_i+f_j)^2) to an ordinary Cheeger estimate by duplicating positive/negative vertices, and preserves the relevant degrees. Thus neither an unweighted graph assumption nor a minimum degree independent of the number of vertices is being imported. Its constants are numerical. The optimizing bipartition may omit a third set: **Theorem 3.2 alone does not control that omitted mass**. Section 3.2 below supplies exactly that missing interface using the planar operator's ordinary spectral gap. This is the crucial check that prevents a word-match argument from masquerading as a reduction.

### 2.3 Existing powers with additional symmetry; concentration literature

**Böröczky–De**, [arXiv:2101.02549v6](https://arxiv.org/abs/2101.02549v6), Theorems 1.4–1.5, already proves factor approximation with exponent (1/(95n)), under (n) common independent linear reflections. Theorem 3.3 obtains a diagonal alignment by applying quantitative Prékopa–Leindler to logarithms of positive orthants. Proposition 4.1 groups diagonal eigenvalues and uses a support excess/cap-volume contradiction to reconstruct coordinate products. These steps explain why power bookkeeping and cap conversion are antecedents; the initial coordinatewise inclusion uses unconditionality. Applying this theorem at (n=2) to arbitrary symmetric bodies would be invalid. The reduction here does not do so.

**Lu**, [arXiv:2608.20730v3](https://arxiv.org/abs/2608.20730v3), Theorem 1.1 records the classical planar case; Theorems 1.2, 1.4 and 1.6 state the higher-dimensional (n-2)-reflection results and equality. The actual statements of the latter theorems use (n\ge3), with the unrestricted plane supplied as the base. Lemmas 4.1–4.2 and Proposition 4.3 use exact fiber equality to keep parallelogram directions fixed and synchronize dilation ratios. They do not provide a uniform finite-deficit synchronization estimate. No extension of this review to those fibers is claimed.

**Böröczky–Henk**, *Cone-volume measure and stability*, [author PDF](https://users.renyi.hu/~carlos/cone-volume-stability.pdf), Theorems 1.1–1.3, proves quantitative near-product conclusions from nearly saturated cone-volume mass on an **exact subspace**, or from near equality in the U-functional. For example, Theorem 1.1 assumes (V_K(L\cap S^{n-1})>(\dim L-\varepsilon)|K|/n). A cloud of small facets near a line need not put any mass on that exact line. Also P10 starts from a two-body Wulff deficit, not that subspace mass. Those hypotheses must be paid before this result applies. Here the linear sine reconstruction gives a more direct transport-to-support estimate, with actual support directions and no appeal to that theorem.

**Hu–Ivaki**, [arXiv:2408.06172v2](https://arxiv.org/abs/2408.06172v2), Theorem 1.1, quantitatively controls a normalized smooth strictly convex body in (L^2) by the oscillation of its cone-volume density relative to a constant. It is a genuine stability theorem, but its data and comparison class are different: small P10 deficit near an oblique parallelogram does not force that density oscillation to be small.

The search also found **Wang–Fang–Zhou**, *Continuity of the solution to the even logarithmic Minkowski problem in the plane*, DOI `10.1007/s11425-018-9531-7`. The primary search extract describes weak convergence/Hausdorff continuity. The full primary PDF fetch returned **HTTP 429**, and a web-open retry was inaccessible. These failures are retained. I do not treat the abstract as an actual theorem/proof audit or rule out every possible quantitative refinement in that paper. This unresolved bibliographic lead limits an exact-priority claim, not the explicit operation reduction below.

### 2.4 Smooth and moment-coordinate sources

**Colesanti–Livshyts–Marsiglietti**, [arXiv:1606.06586](https://arxiv.org/abs/1606.06586), Theorem 1.4, proves validity along small smooth multiplicative perturbations of a ball. **Colesanti–Livshyts**, [arXiv:1710.10708](https://arxiv.org/abs/1710.10708), Theorem 1.1, proves the ball-versus-(C^2)-near-ball inequality with its equality statement; its proof estimates the derivatives of the volume functional in a smooth neighborhood. Neither title licenses an unrestricted deficit-to-(d_{\mathcal E}) power estimate. The latter also explicitly acknowledges its inclusion in Kolesnikov–Milman's theory.

**Wang**, [arXiv:2510.19061v2](https://arxiv.org/abs/2510.19061v2), analyzes the local deficit under adding a segment and gives smooth conditional rigidity. Its adapted perturbation/erosion step is not a uniform nonsmooth endpoint reconstruction. **He–Liu**, [arXiv:2510.21530v1](https://arxiv.org/abs/2510.21530v1), Theorem 4 and Theorem 3.1's proof, uses positive even (C^\alpha) data, regularizes the Wulff support to (C^{2,\alpha}), then differentiates the determinant equation and uses a maximum argument. Those density and regularity constants cannot be replaced by ball bounds without a further proof.

**Liu–Sun–Xiong**, [arXiv:2610.10152v2](https://arxiv.org/abs/2610.10152v2), retains unnormalized tensor squares, the regularizer, moment compactness and boundary flux to classify equality. This is the attributed mechanism reviewed in I45, not an axiom for the external centered theorem and not a quantitative reconstruction theorem used here.

**Klartag**, [*Logarithmically-concave moment measures I*](https://www.math.tau.ac.il/~klartagb/papers/lc_moment.pdf), Theorem 1, assumes a bounded convex target with smooth log-concave density satisfying its condition (2) and yields (\Delta\varphi\le2R(K)^2). The target boundary need not be smooth. It therefore pays I46's hard Gaussian-truncated target Hessian cap. It does not pay the construction of quantitative hard fields, normal-test conversion, or all-dimensional product/endpoint reconstruction in I46 §3.3. No substantive nomination is attached to that conditional budget.

## 3. A noncircular quantitative reduction of P10

All constants in this section depend only on (r,R,\tau), unless explicitly numerical. Constants may change from line to line. First take polygons, with no bound on their number of sides. No estimate below contains the minimum individual facet mass, a minimum angle between arbitrary neighboring normals, or an approximation complexity.

### 3.1 The classical operator and its two spectral facts

At a time with fixed true facets, write (u_i\in\mathbb R/\pi\mathbb Z) for distinct antipodal normal pairs, (s_i>0) for their paired edge lengths, (h_i>0) for supports, and (V=|P|). The classical generating-measure identity and area formula give

\[
 h(u)=\tfrac14\sum_i s_i|\sin(u-u_i)|,
 \quad V=\tfrac12\sum_i h_is_i,
 \quad \nu_i=\frac{h_is_i}{2V},
\]
\[
 T_{ij}=\frac{s_j|\sin(u_i-u_j)|}{4h_i},\qquad
 w_{ij}=\nu_iT_{ij}=\frac{s_is_j|\sin(u_i-u_j)|}{8V}.
 \tag{3.1}
\]

Here (
u) is a probability, (T1=1), and (w) is symmetric. All distinct vertices are joined, so the graph is connected. There are at least two vertices. Individual positive weights can be arbitrarily small.

For completeness, strict negativity on the mean-zero space is a classical mixed-area calculation, not a hypothesis borrowed from P10. The support quadratic form on symmetric bodies is

\[
 V(f,g)=\tfrac12\int_0^{2\pi}(fg-f'g').
\]

On even supports its constant mode is positive and all other Fourier modes are negative; translations are odd and absent. Writing (h=a_0+u), (e=b_0+v) with (V(h,e)=0), the nonconstant norm gives

\[
 -V(e,e)\ge\frac{V(h,h)}{\pi a_0^2}\|v\|_*^2.
 \tag{3.2}
\]

For a vector (y) with (langle y,1\rangle_\nu=0), reconstruct the signed support (e) from masses (s_iy_i). Then (e(u_i)=h_i(Ty)_i), (V(h,e)=0), and (V(e,e)=V\langle y,Ty\rangle_\nu). The piecewise sinusoidal reconstruction is injective (zero values at consecutive true normals force zero between them, as each projective gap is less than (pi)). Thus (T) has spectrum in ([-1,0)) on (1^\perp); the lower bound is the Markov contraction. In particular

\[
 \langle f,(I-T)f\rangle_\nu\ge\operatorname{Var}_\nu f.
 \tag{3.3}
\]

For (h_i(t)=a_i e^{b_it}), let (c=E_\nu b), (q=b-c), and (v=E_\nu q^2). Differentiating the **linear** support reconstruction gives (b=T(s'/s)). Differentiating area gives (V'/V=2c) and (V''/V=2E_\nu b^2+2\langle b,T^{-1}b\rangle_\nu). Hence

\[
 D=-(\log V)''=2\langle q,(-T^{-1}-I)q\rangle_\nu
 \ge2\langle q,(I+T)q\rangle_\nu
 =\sum_{i,j}w_{ij}(q_i+q_j)^2.
 \tag{3.4}
\]

The inequality follows scalar by scalar from (a^{-1}-1\ge1-a) for (0<a\le1). This is the finite planar form of the existing spectral/Bochner operation. It also proves the ordinary gap (3.3), which will be as important as the near-(-1) information.

### 3.2 Dual Cheeger, with the omitted mass fully paid

Suppose (v>0). Write (mu=\lambda_{\min}(I+T)=2-\lambda_{\max}(I-T)). The Rayleigh principle and (3.4) yield

\[
 \mu\le\frac{D}{2v}.
]

Equation (2.1) implies (eta^2\le2\mu) (indeed (mu\ge1-\sqrt{1-\beta^2}\ge\beta^2/2)). Therefore there are disjoint nonempty (A,B), with (S=A\cup B), such that

\[
 \beta\le\sqrt{D/v},\qquad
 w(A,A)+w(B,B)+w(S,S^c)=\beta\nu(S),
 \quad 2w(A,B)=(1-\beta)\nu(S).
 \tag{3.5}
\]

All edge sums are ordered as in (3.1); internal sums include both orientations, and the boundary sum in (3.5) includes one. This explains the normalization.

Apply (3.3) to (1_S). Its energy is (w(S,S^c)), so

\[
 \nu(S)\nu(S^c)\le w(S,S^c)\le\beta\nu(S),
 \qquad \nu(S^c)\le\beta.
 \tag{3.6}
\]

Also (
u(A),\nu(B)\ge w(A,B)\ge(1-\beta)^2/2). Thus for (eta\le1/4), each group has stationary mass at least (9/32). No minimum vertex mass was used. Generic dual Cheeger alone would fail at this step: an almost disconnected bipartite component can coexist with a large nonbipartite remainder. Our exact diagnostic includes that negative control. The planar nonpositive spectrum on (1^\perp) excludes it quantitatively.

### 3.3 From the two groups to two separated actual normals

Let (M=\sum s_i) and (sigma_i=s_i/M). Ball bounds imply (2\pi r\le M\le2\pi R), (pi r^2\le V\le\pi R^2). Consequently, with

\[
 \ell=(r/R)^2,quad U=(R/r)^2,\quad a_*={M^2\over8V},
\]

we have (ell\sigma_i\le\nu_i\le U\sigma_i), and ((\pi/2)\ell\le a_*\le(\pi/2)U). Put (k(u,v)=|\sin(u-v)|). Then (w_{ij}=a_*\sigma_i\sigma_j k(u_i,u_j)).

It follows from (3.5)–(3.6) that

\[
 \sigma(S^c)\le\beta/\ell,\qquad
 m_A:=\sigma(A),\ m_B:=\sigma(B)\ge9/(32U),
\]
\[
 \iint_{A\times A}k\,d\sigma d\sigma,
 \quad\iint_{B\times B}k\,d\sigma d\sigma\le\beta/a_*.
 \tag{3.7}
\]

Average the first internal integral over (a\in A): **some actual vertex normal** (a\in A) obeys

\[
 e_A:=\int_A k(a,u)d\sigma(u)\le\beta/(a_*m_A)\le C\beta.
]

Choose an actual (b\in B) in the same way, with (e_B\le C\beta). The projective angular metric (d\in[0,\pi/2]) satisfies (d\le(\pi/2)\sin d). Move all mass in (A) to (a), all mass in (B) to (b), and the exceptional mass to (a). Its total angular transport cost is at most

\[
 {\pi\over2}\{e_A+e_B+\sigma(S^c)\}\le C\beta.
 \tag{3.8}
\]

These two normals are uniformly separated for sufficiently small (eta), with the threshold depending only on (r/R). Indeed (3.5) gives

\[
 I_{AB}:=\iint_{A\times B}k\,d\sigma d\sigma
 ={w(A,B)\over a_*}\ge {9\over32a_*}.
]

The Lipschitz property of the sine kernel in the projective metric yields

\[
 m_A m_B k(a,b)\ge I_{AB}-{\pi\over2}(m_Be_A+m_Ae_B)
 \ge c(r/R)-C(r/R)\beta.
 \tag{3.9}
\]

Since (m_A m_B\le1), choosing a fixed small (eta_0(r/R)) gives (k(a,b)\ge c_0(r/R)>0). Thus neither a hidden inverse angle nor two coinciding fitted directions is allowed.

Use the same mass transport in the **linear** support representation (3.1). If (h_0) is the reconstructed support from the transported two-point measure, then

\[
 \|h_P-h_0\|_\infty\le {M\over4}\,C\beta\le C\beta.
 \tag{3.10}
\]

It is a parallelogram whose normals are (a,b). For small (eta), (h_0\ge r/2). Replace its two support widths by the original (h_P(a),h_P(b)). The linear coordinate map (x\mapsto(a\cdot x,b\cdot x)) and (3.9) show that each vertex changes by (O(\beta)). The resulting parallelogram

\[
 Q=\{|a\cdot x|\le h_P(a),\ |b\cdot x|\le h_P(b)\}
]

therefore obeys

\[
 P\subset Q,qquad d_H(P,Q)\le C\beta\le C\sqrt{D/v}.
 \tag{3.11}
\]

This completes every mass, angular, support and active-normal interface. It uses no facet-count bound or minimum facet mass.

It also directly subsumes I46's particular three-region budget: if (sqrt{D/v}\le c s^2), (3.8) and Markov's inequality leave mass at most (s) outside the two radius-(s) neighborhoods. Otherwise (v\le C D s^{-4}). Thus the masses (s,s,s^2) and the (s^{-4}) loss in I46 §4.3 are not an indispensable new mechanism; the available dual Cheeger operation supplies that dichotomy and, using transport directly, a better one.

### 3.4 One interior time, without a facet or chamber constant

For polygon endpoints the union of endpoint normal directions describes the full Wulff interpolation. On each cone between consecutive union normals the two endpoint supports are positive linear combinations of their values on those rays; Hölder proves the intermediate constraints are implied by the union constraints. A finite exponential-polynomial event partition gives finitely many changes of true facets; no quantitative bound on its size is required.

Classical planar logBM gives concavity of (\log|P_t|): more generally (\mathcal W[h_A^{1-s}h_B^s]\subset\mathcal W[f^{1-s}g^s]) when (A=\mathcal W[f]), (B=\mathcal W[g]). Let

\[
 g(t)=\log|P_t|-(1-t)\log|K|-t\log|L|.
]

Concavity, (g(0)=g(1)=0) and (g(\lambda)=\delta) give (0\le g\le\delta/\tau), and at differentiability times (t\in[1/4,3/4]), (|g'(t)|\le4\delta/\tau). The Green kernel (G_\lambda(t)=\min\{(1-\lambda)t,\lambda(1-t)\}) satisfies (G_\lambda\ge\tau/3) on ([1/3,2/3]). Since (-g'') is a nonnegative measure,

\[
 \int_{1/3}^{2/3}D(t)dt\le3\delta/\tau.
]

There exists a nonexceptional (t\in[1/3,2/3]) with (D\le C_\tau\delta). At the **same time**, with (c=E_\nu b),

\[
 2c=\log|L|-\log|K|+g'(t),
 \quad\log(|K|/|P_t|)+2tc=-g(t)+tg'(t)=O_\tau(\delta).
 \tag{3.12}
\]

All (P_t) lie between the original balls, and (|b_i|=|\log(h_L(u_i)/h_K(u_i))|\le\log(R/r)). No selection of a uniformly long chamber was made.

### 3.5 Both endpoint interfaces

The Fourier calculation (3.2), followed by one-dimensional Sobolev/Fourier summation, gives the classical mixed-area remainder, for symmetric (A) between fixed balls and any symmetric (B),

\[
 d_H(B,aA)^2\le C(r,R)\{V(A,B)^2/|A|-|B|\},
 \qquad a=V(A,B)/|A|>0.
 \tag{3.13}
\]

Explicitly the nonconstant Fourier weights are (4j^2-1); their inverse sum is finite, controlling the supremum norm, and (|A|/(\pi a_0^2)\ge(r/R)^2) in (3.2). This is uniform for all even (H^1) support functions. It does not assume smooth curvature.

At every current true facet, (h_K=h_Pe^{-tb}). Thus

\[
 V(P,K)/|P|=E_\nu e^{-tb}
 \le e^{-tc}(1+Cv).
]

Taylor's formula on the fixed bounded interval for (b-c) proves the last inequality; the linear term has mean zero. Equation (3.12) then bounds the mixed-area defect by (C(v+\delta)). The same computation for (L) yields a homothetic comparison pair ((a_KP,a_LP)\in\mathcal E) with

\[
 d_{\mathcal E}(K,L)\le C\sqrt{v+\delta}.
 \tag{3.14}
\]

This estimate always holds, not only in a predetermined branch. Both coefficients average positive bounded support ratios, so they are positive and uniformly bounded. If (v=0), (3.14) already suffices.

If (v>0) and (sqrt{D/v}\le\beta_0), take the **actual active** (a,b) furnished by §3.3 and define

\[
 Q_0=\{|a\cdot x|\le h_K(a),\ |b\cdot x|\le h_K(b)\},\quad
 Q_1=\{|a\cdot x|\le h_L(a),\ |b\cdot x|\le h_L(b)\}.
]

They contain (K,L), have a uniform outer radius by (3.9), and share the same two edge directions. Their two-width logarithmic interpolation is exactly (Q) in (3.11), **because** (a,b) are active for (P_t). Its area is the product of its widths times (4/|\det(a,b)|), so

\[
 (1-t)\log{|Q_0|\over|K|}+t\log{|Q_1|\over|L|}
 =g(t)+\log{|Q|\over|P_t|}
 \le C(\delta+\sqrt{D/v}).
 \tag{3.15}
\]

The last bound follows from (3.11) and (P_t\supset rB): an additive support error (eta) gives (Q\subset P_t+\eta B\subset(1+\eta/r)P_t). Each summand in (3.15) is nonnegative and (t,1-t\ge1/3); hence each endpoint area excess is at most (C(\delta+\sqrt{D/v})).

Finally, for (rB\subset A\subset B\subset R_1B), an exposed point of support excess (eta=d_H(A,B)), joined to the radius-(r) segment perpendicular to that support direction, creates a triangle outside (A) of area at least (c(r,R_1)\eta^2). Thus (d_H(A,B)^2\le C(|B|-|A|)). Apply this to both endpoints of (3.15):

\[
 d_{\mathcal E}(K,L)\le C\sqrt{\delta+\sqrt{D/v}}.
 \tag{3.16}
\]

The constructed ((Q_0,Q_1)) belongs to the full allowed class, even when the normals and edge subspaces are oblique. No scalar (q) was incorrectly used to identify the two endpoint widths; those widths came from actual supporting lines and nonnegative area losses.

### 3.6 Balance, degenerate cases, and arbitrary bodies

For sufficiently small (0<\delta<\delta_0(r,R,\tau)), split at (v=\delta^{1/3}). If (v\le\delta^{1/3}), (3.14) gives (d_{\mathcal E}\le C\delta^{1/6}). Otherwise (D\le C\delta) gives (sqrt{D/v}\le C\delta^{1/3}\le\beta_0), and (3.16) gives the same conclusion. This is the explicit chain

\[
 D\le C\delta,quad
 \beta\le\sqrt{D/v},quad
 d_{\mathcal E}\le C\min\{\sqrt{v+\delta},\sqrt{\delta+\beta}\}
 \ \Longrightarrow\ d_{\mathcal E}\le C\delta^{1/6},
 \tag{3.17}
\]

where the second entry of the minimum is used only when (eta\le\beta_0). If (delta=0), replace it throughout by any positive upper bound (arepsilon) and let (arepsilon\downarrow0). This proves (d_{\mathcal E}=0), sufficient for the claimed inequality, without asserting closedness of (mathcal E). For larger deficits, (d_{\mathcal E}\le R) by comparison with ((rB,rB)); adjust the constant. Consequently (delta\ge c d_{\mathcal E}^6\ge c\max(1,R)^{-4}d_{\mathcal E}^{10}).

Approximate arbitrary symmetric endpoints by symmetric polygons between ((r/2)B) and (2RB). The preceding constants are independent of their facets, masses and angles. Uniform convergence of their positive supports gives multiplicative convergence of the interpolated support bounds. The corresponding Wulff bodies are bracketed by the same multiplicative dilates, so their deficits converge. Distance to a fixed subset of a metric space is 1-Lipschitz, so (d_{\mathcal E}) converges too. This proves the reduction for **all** bodies in the stated class, not a fixed-facet Łojasiewicz assertion or a compactness modulus without a power.

This argument does not use the I46 three-region lemma, P10, E, LSX, or the Q obstruction as premises. Its geometric interfaces were proved here from linear reconstruction and scalar estimates. That is why it is a noncircular operation-level reduction rather than a paraphrase of the author's proof.

## 4. Deep comparison with Xi's September 2026 three-step proof

The actual [arXiv:2609.08495v1](https://arxiv.org/abs/2609.08495v1) Theorem 1.1 concerns bodies at a dilation position, every (p\in[-\infty,0]), every auxiliary (mu>0), and the minimum of two relative-radius expressions. Its statement gives sufficient equality examples; §2 explicitly declines a complete equality characterization. One must not silently read an “if and only if” quantitative theorem into it.

Here is the quantitative information **actually retained by all three steps**, rather than an appeal to an unprinted rate. Independently rescale the symmetric endpoints to area one; the rescalings and new ball bounds depend only on the original (r,R). For the midpoint let (M=\mathcal W[\sqrt{h_Kh_L}]), (m=|M|\ge1), (C=K+L). Let (t\in\{r(K,L),R(K,L)\}) maximize (H=\sqrt t+1/\sqrt t). The support ratio is uniformly bounded above and below. Xi's steps are

\[
 Hm\ge V(M,C),\qquad V(M,C)^2\ge m|C|,
 \qquad |C|=2+2V(K,L)\ge2+t+t^{-1}=H^2.
 \tag{4.1}
\]

The last inequality is the correctly normalized relative Bonnesen inequality (2V(K,L)\ge t+t^{-1}), as in BLYZ Theorem 4.1. With (epsilon=m-1), (4.1) pays

\[
 0\le |C|-H^2\le H^2\epsilon,
 \quad 0\le {V(M,C)^2\over m}-|C|\le H^2\epsilon,
 \quad 0\le Hm-V(M,C)\le H(m-\sqrt m)\le C\epsilon.
 \tag{4.2}
\]

Thus (3.13) already yields (C\) within (C\sqrt\epsilon) of a dilate of (M); the Bonnesen slack at the selected radius is (O(\epsilon)). At surface-area-almost every contact direction of (M), writing (x=h_K/h_L), the first slack has the exact representation

\[
 Hm-V(M,C)
 =\frac12\int h_M(u)\{H-\sqrt{x(u)}-1/\sqrt{x(u)}\}\,dS_M(u).
 \tag{4.3}
\]

This is stronger usable information than merely noting that the paper does not print a rate. However, (4.3) controls **support-ratio values**, not the geometric separation of the normals carrying them. The second estimate in (4.2) controls the **sum body** (K+L), not two endpoints with compatible equality factors. Near equal radii the scalar two-well separation degenerates; when the radii stay separated a quantitative version of the Bonnesen endpoint/segment reconstruction and synchronization would still be needed. BLYZ's exact inner-parallel-body equality argument cannot be cited as that quantitative assertion without controlling the endpoint loss.

I do **not** claim a complete P10 reduction from Xi's printed three inequalities alone. Nor do I claim these remaining interfaces are impossible. The verdict instead rests on the complete graph reduction in §3, whose near-parallelogram interface is fully paid. Xi's note is a strong alternate starting point and supplies explicit scalar remainders, but it is not the exact-duplicate witness. The midpoint restriction is also not an obstacle by itself: concavity gives (\Delta_{1/2}\le C_\tau\Delta_\lambda); the unpaid issue in that route is geometric endpoint reconstruction, not the parameter (lambda).

## 5. Interpretation of the significance verdict

The exact new-to-this-report computation is the application of a standard weighted near-bipartiteness theorem to the classical planar inverse kernel, with the short mass/transport/endpoint interfaces in §3. It is appropriate to credit I46 for formulating and proving a uniform elementary planar estimate; it is inappropriate to infer substantial discovery solely from the lack of a printed exponent 10. The reduction supplies even its difficult quantifiers using existing proof operations and explicit elementary inequalities. This is the project's TECHNICAL ONLY category, not a claim that the application is literally quoted in an older paper.

In particular:

* **Exact duplication:** not established. The primary search was bounded, with a retained inaccessible continuity-paper lead. No worldwide absence or priority is certified.
* **Operation-level reduction:** established in §3 without using P10 or I46's cluster lemma as a premise. The missing-third-set error in a generic Cheeger argument was explicitly repaired by the pre-existing negative spectrum of the planar mixed-area operator.
* **Original proof:** outside this verdict. I47 was not read and no PASS is attributed to it. Finite exact arithmetic and source hashes are not an analytic audit.
* **Upstream enablement:** the reduction uses classical planar logBM, mixed-area reconstruction, dual Cheeger, and cap/area estimates. It needs no new OpenAI theorem or proof operation. Thus it also fails the user's original enablement gate independently of the numerical exponent.
* **Remaining research scope:** no unrestricted higher-dimensional finite power, sharp planar cubic result, quantitative Lu fiber synchronization, or all-dimensional hard moment-field reconstruction is obtained. The intermediate exponent six is not separately nominated or advertised as sharp.

## 6. Evidence freeze and reproducible checks

Only the authorized I48 report/source/experiment paths were written. No shared/prior edits, staging, commits, publication, or additional agents were used. All four shared ledgers are explicitly mutable; historical seals are checked without refreshing them. The actual pinned blob identities and complete 9,340-file inventory are verified against the 13,223-entry tree, not the truncated root-tree cache or a 719-paper catalogue count.

The independent `check.py` uses exact rational arithmetic, rational unit normals and paired curvature masses. Its nine sine-graph configurations include oblique anchor pairs and small-angle/small-mass fixtures down to a mass (1/34359869441). It checks weighted normalization, strict negativity on the mean-zero subspace by exact leading minors, the ordinary-gap cut bound for every subset, the dual-Cheeger inequality as a full-matrix PSD certificate (all principal minors), the omitted-mass and two-group lower bounds, actual-normal selection, transport and support-error estimates, and containment of every explicitly generated zonotope vertex in the active-normal enclosing parallelogram. Two negative controls show that dual Cheeger without the ordinary-gap hypothesis does not control the remainder. The diagnostic passes **1,830 exact assertions**. The Xi slack and exponent checks are supplementary; they are not the only tests.

These finite tests cannot certify the universal analytic inequalities, approximation limit or literature significance. Those arguments are written in §§3–4. A preparation typo in an auxiliary `sed` range is recorded as an inspection-command failure; it did not alter an input or a mathematical fixture. The HTTP 429 continuity response and failed web retry are preserved, not relabeled as a successful proof read.

Run from the project root:

```sh
python frontier/experiments/i48_planar_logarithmic_stability_novelty/check.py
python frontier/experiments/i48_planar_logarithmic_stability_novelty/verify.py
```

`verify.py` is read-only, disables bytecode, checks the exact I48 artifact set and frozen inputs, primary response and version bindings, literal passage extracts, selected pinned blobs, whole-corpus hashes and searches, and the unchanged I43/I44/I45/I46 seals. It compares the exact diagnostic output without modifying old verifiers or seals. Mutable shared-ledger drift is reported separately. The original I46 parent evidence PASS is frozen as historical evidence, not recast as proof approval. The parent may integrate this review with I47 when that independent audit is available.
