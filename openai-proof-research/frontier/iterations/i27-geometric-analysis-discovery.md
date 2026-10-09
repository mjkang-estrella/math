# I27 geometric analysis: endpoint-center retention is still missing

**Disposition: investigated gap, with explicit obstruction tests and two developed endpoint arguments. No substantial theorem is submitted, no finding number is assigned, and no count changes.** The strongest target is countable codimension-one rectifiability of the full Euclidean stationary-varifold singular set, including singular points with planar tangents. The source gives its Hausdorff dimension, but its center-retention estimate is strictly supercritical. This report identifies the precise divergent term, constructs smooth limiting-system countermodels to a proposed automatic repair, and derives the quantitative frequency estimate available after retention. These are research diagnostics and technical deductions, not a solution of the target.

All pinned proofs are premises, not objects of an upstream truth audit. The three screens are Einstein metric stability, supercritical-scalar Ricci-flow continuation, and varifold endpoint rectifiability. None recycles the parked spectral, topology, arithmetic, kinetic, or height routes. The frozen ledger has four accepted findings. I25's separate proof/significance process has no bearing on this report's verdict.

## 1. Scope, freeze, and sources

The upstream revision is `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. [Task brief](../sources/i27_geometric_analysis_discovery/task-brief.txt), [input manifest](../sources/i27_geometric_analysis_discovery/input-manifest.json), [source manifest](../sources/i27_geometric_analysis_discovery/source-manifest.json), [exact statement inventory](../sources/i27_geometric_analysis_discovery/source-contracts.json), and [actually read proof passages](../sources/i27_geometric_analysis_discovery/source-read-passages.json) distinguish retained sources from mathematical reading.

The complete inventory has 749 manuscript directories. All 9,340 read-only cache texts were checked against their SHA-256, size and Git blob identities; the verifier also compares them with the complete tree. Only the 96 text files in the eight selected manuscripts were copied. The truncated root tree was not used. Whole-corpus normalized-text screens are retained separately; they are discovery aids, not semantic reading of 749 papers or a priority argument.

The I14/I15/I17 final significance reviews were consulted for their decisive reductions: general-coefficient local surface estimates already available in primary proofs; iteration of marked annulus replacement; and two adjugate lifts followed by multiplication. Accordingly, all operations inside the present source proofs count as existing machinery. In particular, I do not present the Einstein paper's high-curvature-tail smoothing or the varifold paper's prescribed-scale fitting as new bridges.

For compact references below, the eight source names are:

- **E+**: `Positively-curved-Einstein-four-manifolds-September-23-2026`.
- **E0**: `Zero-Plane-Rigidity-for-Einstein-Four-Manifolds-October-4-2026`.
- **EG**: `An-L2-Einstein-Gap-for-Nonnegatively-Curved-Four-Manifolds-October-5-2026`.
- **RF4**: `Bounded-scalar-curvature-and-smooth-extension-of-four-dimensional-Ricci-flow-September-24-2026`.
- **RFH**: `A-closed-Ricci-flow-with-bounded-scalar-curvature-and-finite-time-curvature-blowup-September-24-2026`.
- **RT**: `Path-selection-and-an-elliptic-inequality-on-degenerating-Ricci-flat-trees-September-24-2026`.
- **AE**: `Almost-everywhere-regularity-of-stationary-integral-varifolds-September-23-2026`.
- **VD**: `A-Codimension-One-Bound-for-the-Singular-Set-of-a-Stationary-Integral-Varifold-October-5-2026`.

Every source file has its immutable raw URL and blob hash in the manifest. For example the decisive [VD density-center proof](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Codimension-One-Bound-for-the-Singular-Set-of-a-Stationary-Integral-Varifold-October-5-2026/build/sections/06b-density-centers.tex) and [EG complete proof](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-L2-Einstein-Gap-for-Nonnegatively-Curved-Four-Manifolds-October-5-2026/build/source/main.tex) are pinned to that revision.

## 2. Screen A: quantitative stability of the original almost-Einstein metric

### Exact contracts and the target

E+ `thm:classification` classifies every connected smooth closed Einstein four-manifold with **strictly positive sectional curvature**, without orientability, up to positive rescaling and isometry as round S4, round RP4 or Fubini–Study CP2. E0 `thm:main` assumes `Ric=3g`, `sec≥0` on a connected closed four-manifold; one zero plane forces universal cover S2(1/√3)×S2(1/√3). Its `cor:nonnegative-classification` adds that this cover, round S4, and normalized CP2 exhaust the nonnegative class.

EG `thm:gap` assumes a connected **simply connected**, smooth closed four-manifold, `sec≥0`, and

\[
\mathcal D(g)=\int_M|\operatorname{Ric}-Rg/4|^2\,d\mu<\varepsilon_0.
\]

It concludes only the three smooth diffeomorphism types. The integral is not volume-normalized and is scale invariant in dimension four. There are no extra geometry bounds. Its stronger `prop:limit` already gives, after average-scalar normalization `V^{-1}∫R=12`, subsequential diffeomorphisms and smooth convergence of the **positive-time unnormalized flows** to `(1−6t)h`, for every compact time interval in `(0,T)`, with `Ric_h=3h`, `sec_h≥0`.

A meaningful new target would be universal constants `C,θ,ε>0` with

\[
\min_{h\in\{h_{S^4},h_{CP^2},h_{S^2\times S^2}\}}
 d_{GH}((M,d_g),(M_h,d_h))\le C\mathcal D(g)^\theta
 \tag{E-target}
\]

for all the normalized EG metrics with `D<ε`. The comparison is between compact metric spaces; no identification of manifolds is built into its definition. A stronger deformation statement would need to specify a gauge and a dynamics that actually converges. Neither statement is proved here.

### Existing machinery and the two obstructions

EG already derives `||R−12||_2≤4||E||_2`, `||Ric−3g||_2²≤5D`, lower volume from Euler characteristic and Chern–Gauss–Bonnet, upper diameter from segment averaging and the index form, then upper volume. Its support/truncation argument supplies a uniform Sobolev constant. With `w=(|Rm|−K(t))_+`, it proves `||w(t)||_2²≤e^{Ct}||w(0)||_2²`, uniform noncollapse, a common lifespan, and `|Rm(t)|≤A/t`. A homogeneous equation for `Ric−3g/(1−6t)` propagates the small defect. Finally `∫(−sec)_+≤Ct` and the exact scaling of the Einstein limiting flow recover `sec_h≥0`. Thus obtaining these uniform bounds again, or classifying the already smooth positive-time limit, is not a discovery.

The remaining time-zero metric interface is real. A bound of order `C sqrt(D)/t` for the smoothed Einstein error, even if established, integrates as `sqrt(D) log(t/s)` between positive times; it gives no uniform control as `s↓0`. Fixing `t>0`, taking the sequence limit, and then sending `t↓0` does not identify the original distance functions without a separate distortion estimate. The original nonnegative sectional curvature can be useful, but it must enter a new estimate, not an assertion that it persists under four-dimensional Ricci flow.

This is consistent with the precise scope of Martens' [2408.11115v2](https://arxiv.org/abs/2408.11115v2), Theorems 1.1–1.2 and Remark 1.3: local volume upper bounds, local entropy and small critical curvature concentration yield smoothing and metric-measure compactness, but that theorem explicitly does not guarantee distance convergence of its positive-time flow back to the initial distance. Chan–Chen–Lee [2102.12840v3](https://arxiv.org/abs/2102.12840v3), Theorem 1.2, assumes an initial Ricci lower bound, entropy bounds and small local full-curvature concentration; it gives short-time `Cε/t` curvature and `c√t` injectivity estimates. These statements are not an original-metric power rate for EG's defect.

The simplest proposed dynamics is actually false. Let `g=a g_S2+b g_S2`, where the unit spheres have curvature one. Then

\[
 R=2/a+2/b,\quad \mathcal D=16\pi^2(a-b)^2/(ab).
\]

Set `a=[3(1+u)]^{-1}`, `b=[3(1−u)]^{-1}`, `|u|<1`. The metric has `R=12`, `sec≥0`, and

\[
 \mathcal D=64\pi^2u^2/(1-u^2)\longrightarrow0.
\]

For volume-normalized flow `∂_t g=−2Ric+(R/2)g`,

\[
 a'=a/b-1,\quad b'=b/a-1,\quad (ab)'=0,\quad
 (a-b)'=(a-b)(a+b)/(ab).
\]

If `a<b`, then `a'=a²/(ab)−1<0` and remains at most its initial negative value. Thus `a` reaches zero in finite normalized time and `b` diverges; it cannot converge to the equal product. Equality `a=b` is stationary. This disproves universal convergence of normalized Ricci flow from arbitrarily small EG defect. It does **not** refute E-target or a different carefully chosen deformation. The formulas are a classical product calculation, not a substantial finding.

**Screen disposition:** a positive-time stability corollary is technical; original-metric quantitative stability remains open here; the proposed universal normalized-flow deformation fails. The missing distance/gauge estimate is not supplied by existing compactness alone.

## 3. Screen B: replace bounded scalar curvature by spatial Lp, p>2

### Contracts, scope comparison, and existing proof operations

RF4 `thm:extension` assumes a smooth Ricci flow on a closed connected smooth **four-manifold**, smooth initial metric, finite `T>0`, and `sup_{M×[0,T)}|R|<∞`. It extends smoothly on the **same manifold** beyond T.

RFH `thm:main` gives a counterexample on `S2×S^{q+1}` for a sufficiently large integer `q≥10`, hence dimension `q+3`, not four. Its `cor:rates` fixes any sufficiently large q and then any sufficiently large even k, with constants depending on that flow, obtaining two-sided curvature rate `(T−t)^{-2k/d_q}`, where `d_q=(q+1−sqrt((q+1)(q−7)))/2`. The cap/barrier proof chooses `a=5/2`, q for a positive diffusion-reaction margin, then k so the spatial Ricci exponent `e=a−d_q+d_q/k` lies in `(0,1)`. The scalar barrier and two-sided rates are already inside the source. Neither dimensional interpolation nor another mode-index consequence is a new mechanism.

RT `thm:tree-inequality` fixes a **finite** Ricci-flat four-dimensional rooted tree and matching nontrivial quotient groups on joined ends. Length ratios are `a_child/a_parent=e^{-2L_e}`. All `L_e→∞` independently. Compact vertex convergence, uniform metric end bounds through order 20, joining decay exponent `μ>0`, root decay `q>1`, and a weighted dimensionless Ricci error `M→0` through order 10 give `E(g)=o(M)` in root units. The constants may depend on the fixed tree; no universal power exponent is asserted. `M=0` means `E=0`. The renormalized functional scales as length squared and satisfies

\[
 DE_g(\dot g)=\int\langle Rg/2-\operatorname{Ric},\dot g\rangle\,d\mu.
\]

Its proof already retains kernels/cokernels, builds the augmented analytic family, compares the original metric up to `O(M)` with observable error `O(M²)`, and uses finite weighted variation along selected analytic paths to rule out `F²≥cJ` as `F→0`. RF4 already supplies actual-flow tree selection, Bianchi removal of the critical radial mode, faster-than-`r^{-2}` annular Ricci decay, a fixed-material-collar extension, and time-patch functional variation. A new result must establish these inputs under a genuinely weaker hypothesis.

### New target and a precise failed extension

For every finite `p>2`, a meaningful target is: a closed four-dimensional smooth flow with

\[
 \sup_{0\le t<T}\int_M|R|^p\,d\mu<\infty
 \tag{R-target}
\]

extends smoothly on M. This is not obtained by applying RF4 because an Lp bound is not an L∞ bound. At curvature rescaling `g'=λg`,

\[
 \|R(g')\|_{L^p(g')}=\lambda^{2/p-1}\|R(g)\|_{L^p(g)}.
\]

Consequently any **already smoothly convergent** spacetime blowup with `λ→∞` has scalar zero at each interior time; the scalar evolution then makes its Ricci tensor zero. This computation explains plausibility, but neither supplies the smooth convergence nor excludes nonflat Ricci-flat bubbles.

Liu–Simon [2410.08667v2](https://arxiv.org/abs/2410.08667v2), Theorem 1.1, gives noncollapse, a four-dimensional L2 full-curvature bound and an improved spacetime Ricci bound from a uniform spatial scalar exponent `2+12α`, `0<α<1/12`, with their local setting (B); on the full closed manifold the boundary conditions disappear. Theorem 1.4 gives an orbifold limit and continuation by **orbifold** Ricci flow from exponent `2+σ`, `0<σ<1`. Their displayed flow convention in that theorem differs by a constant time factor, irrelevant to these distinctions. Any fixed `p>2` permits lowering to such an exponent using the finite-time volume upper bound. This is substantial available compactness, but is not smooth continuation on M.

A decisive obstruction to simply repeating RF4 occurs in `final:variation`. The true-core integrand is

\[
 2|\operatorname{Ric}|^2-R^2.
\]

In RF4's interval units `|R|≤Cε_i²`; the core has volume `O((Na)^4)`, and N is fixed before `i→∞`. Thus the scalar-square loss is `O(ε_i^4 N^4 a^4)=o_i(a^4)`, the same normalization as root energy. Replace that pointwise bound by `||R||_p≤δ_i→0`. Hölder gives only

\[
 \int_{B(Na)}R^2\le C\delta_i^2(Na)^{4-8/p},\qquad
 a^{-4}\int_{B(Na)}R^2\le C_N\delta_i^2a^{-8/p}.
 \tag{R-loss}
\]

There is no relationship in the hypothesis between the outermost tree scale a and δ_i. Even vanishing rescaled scalar norm does not make R-loss small. For a diagnostic take a function equal to `δ/a^{4/p}` on a region of volume `a^4` and zero elsewhere. Its Lp norm is δ while the normalized square loss is `δ²a^{-8/p}`. With `a=δ^{p/2}`, that loss is `δ^{-2}`. Its amplitude `δ^{-1}` is still below `a^{-2}` for `p>2`; even a crude curvature-scale cap would not repair this inference. These are scalar functions, **not** constructed Ricci-flow counterexamples.

At p=2 the scalar norm is scale invariant and even its blowup vanishing fails; at p=∞ the scalar-square estimate returns to RF4. No endpoint p=2 extension is proposed.

The independent geometric side also needs reproof: RF4 `para:source-scale` uses `|Ric|_{j,r}≤C_j ε/r`, controlling motion in material coordinates and the cutoff forcing. A formally weaker power `r^{-1-2/p}` might leave a positive exponent margin for `p>2`, but no proof here establishes the full annular estimates, the scalar-square compensation, and their compatibility on moving cores. In particular RT's fixed-tree little-oh cannot absorb a separate negative term that is not `o(a^4)`.

**Screen disposition:** R-target remains unproved. The identified normalized scalar-square obstruction is more specific than saying “compactness is missing.” Proving bubble compactness alone or restating RT with assumed weighted estimates would not settle it. The high-dimensional examples do not answer R-target either way.

## 4. Screen C and selected target: endpoint rectifiability

Fix integers `m≥2`, `n≥1`, an open Euclidean set `U⊂R^{m+n}`, and a locally finite stationary integral m-varifold V. No stability, minimizing property, orientability, multiplicity cap or graphical representation is assumed. Regularity means `V=q|Σ|` on a neighborhood for a smooth embedded minimal Σ and a positive integer q, including equality of the **entire** local support. Let

\[
 \mathcal B_Q=\{x\in\operatorname{Sing}V:
       Q|\Pi|\text{ is a tangent varifold for some m-plane }\Pi\},
 \qquad \mathcal B=\bigcup_{Q\ge2}\mathcal B_Q.
\]

The zero varifold and empty singular set are vacuous cases; all arguments are local away from the boundary of U. The intended conclusion is that `Sing V` is countably `(m−1)`-rectifiable: it is covered, up to H^{m−1}-null sets, by countably many Lipschitz images of bounded subsets of R^{m−1}. Local finiteness of H^{m−1} and a mass-only bound are **not** part of this target. Countable rectifiability does imply σ-finiteness, so silently working only with finite-measure pieces would leave another gap.

These sets are measurable. The regular set is relatively open. Density exists everywhere by stationary monotonicity and is upper semicontinuous. On each relatively compact ambient region, choose a countable metric of weak varifold convergence on successively larger balls. Having a subsequence of rescalings converge to a Q-plane is expressed by countable intersections/unions of approximation conditions, with rational radii and a countable dense family of planes. Continuity of pushforward integrals at positive radii and compactness of the Grassmannian give equivalence with the original tangent condition. Thus each B_Q is Borel. Density-one planar tangents give regularity by Allard, explaining Q≥2.

AE `thm:main` gives `H^m(Sing V)=0`. VD `thm:main` gives `dim_H Sing V≤m−1`, for every m,n≥1. Neither says endpoint rectifiability. Naber–Valtorta [1505.03428v4](https://arxiv.org/abs/1505.03428v4), Theorems 1.3–1.5, give quantitative-stratum packing and countable k-rectifiability of

\[
 S^k(V)=\{x:\text{no tangent cone is }(k+1)\text{-symmetric}\}.
\]

The part `Sing V\B` is `S^{m−1}` and is already covered. Planar tangents are m-symmetric, so B is exactly the difficult residual. A dimension bound on B is not a proof that it is rectifiable.

The strongest current direct comparator is Krummel–Minter–Wickramasekera [2606.01511v1](https://arxiv.org/abs/2606.01511v1), Definition 1.2 and Theorem A. Their class must be closed under weak limits, homotheties, rotations and disjoint decomposition, and satisfy a quantitative ε-regularity hypothesis at multiplicities up to Q. With a mass cap `<Q+1/2` and small cylindrical height, that hypothesis supplies actual Lipschitz multigraph representation, generalized C^{1,α} regularity, tangent-cone variation and excess-decay estimates. They prove branch dimension ≤m−2 at density Q. Their applications include two-valued Lipschitz stationary graphs and stable codimension-one classes excluding lower-density classical singularities. This already gives the desired endpoint rectifiability **in those classes**, using Naber–Valtorta on the remainder. AE regularity almost everywhere and VD's fitting graphs do not establish that ε-regularity hypothesis for arbitrary V.

Hirsch–Spolaor [2401.00279v1](https://arxiv.org/abs/2401.00279v1), Theorem 1.2, requires an actual stationary two-valued Lipschitz graph. Brena–De Lellis–Franceschini [2503.00649v1](https://arxiv.org/abs/2503.00649v1), Theorems 1.2–1.3, and Kolasiński [2609.19979v1](https://arxiv.org/abs/2609.19979v1), Theorem 1.1, concern smooth rectifiability of the m-dimensional carrier or almost-everywhere approximation, not H^{m−1} structure of its singular set. No theorem in those precise contracts removes the residual B.

The selected target therefore needs a new endpoint-center or multiscale geometric bridge. It is not another application of standard tangent-cone dimension reduction.

## 5. Complete source interface used in the endpoint attacks

VD `prop:flat-scales` starts from `m−1<s<dim_H Sing V`. At one fixed singular origin it supplies radii `L_i↓0`, `V_{L_i}⇀Q|Π|`, and measures σ_i on **exact density-Q singular centers** in the ambient closed unit ball, with `c≤σ_i(B_1)≤C` and `σ_i(B_r(X))≤Cr^s`. The strict inequality s>m−1 is already used here to make the support of a limiting center measure span m independent directions, forcing a planar cone. It is not permissible to set s=m−1 in this proposition verbatim.

The following stronger operations are nevertheless present in the proof and have been inspected:

1. AE's signed excess uses `M=π_#μ−Q vol_S`, tilt D, geometric error Λ, and `τ=|M|+D+Λ`. For fixed Q and κ, `τ(B_4)≤d=e^{-T}` and physical radius plus support height at most `e^{-κT}` imply `∫w(2M−D−C_QΛ)≤d e^{-F_Q(T)}` for normalized nonnegative Lipschitz tests. `F_Q(T)=exp_{2Q}(sqrt(log_{2Q}T))`. The flat-reference form drops Λ and the second smallness condition. There is no pointwise density bound θ≤Q.
2. VD `lem:local-fits` imports AE's minimal fits, first-moment estimates, compatibility and lower-multiplicity separated entries at a failed fit **before** AE uses its multiplicity-defect density assumption. VD's tents glue a C^J center, with mean-curvature bounds `Cm_0²t^{2k−4}` and support height `Cm_0t^k`. This is stronger than simply knowing almost-everywhere regularity.
3. VD `prop:target-frequency` covers all sufficiently late prescribed flat scales, including restart transitions. Its proof uses the preceding failure for an outer frequency bound and the current failure for an inner bound. The constants are uniform for that sequence. This avoids changing to a more convenient subsequence that loses the selected centers.
4. VD `prop:centered-blowup` sets `a_i=√H(r_i)/r_i→0` and obtains centers S_i with `D_i+|M_i|=O(a_i²)`, support height `|z_i|≤Ca_i`, `|H_{S_i}|+|∇^⊥H_{S_i}|=o(a_i)`, vanishing normalized first moment, and a nonzero normalized second moment. Its proof includes uniform support control via a mean-value inequality, not only integral height control.
5. VD `prop:linearized` passes to Radon measures `(ν,f,β,𝔪)`, with `ν≠0`, `d_0=tr β`, satisfying

\[
 \mathcal M=\begin{pmatrix}\nu&f^t\\ f&\beta\end{pmatrix}\ge0,
 \quad \nabla\nu=2f,\quad\operatorname{div}f=d_0,
 \quad\operatorname{div}\beta=\nabla\mathfrak m,
 \quad2\mathfrak m\le d_0,\quad|\mathfrak m|\le C d_0. \tag{V-system}
\]

The last divergence identity is distributional. The proof uses slow physical dilation, cell budgets with a floor and signed excess to remove geometric errors after division by a_i². It deliberately allows concentrated tilt and does not identify a harmonic multigraph.

VD `prop:density-comparison` retains the σ_i centers in this height blowup. For every limiting center x and every sufficiently small l, it proves

\[
 2l^2\int\phi_{x,l}\,d\mathfrak m\ge\int\psi_{x,l}\,d\nu,
 \quad \phi_{x,l}=l^{-m}(1-|y-x|^2/l^2)_+^p,
 \quad\psi_{x,l}=2pl^{-m}(1-|y-x|^2/l^2)_+^{p-1}, \quad p\ge4. \tag{V-center}
\]

The cutoff p here is unrelated to the scalar integrability exponent in Screen B. VD `prop:measure-reduction` then shows that the set of such centers has dimension at most m−1. The two attacks below concern the endpoint interface, not an audit of any of these stipulated conclusions.

## 6. Attempt A: retain endpoint centers by compensated averaging

### The exact error and the order of limits

There is a preliminary matching problem as well. At a point of B_Q, existence of some flat tangent scales does not imply that those same scales carry a lower bound `c r^{m−1}` for a chosen endpoint center measure. Positive upper density of that measure supplies another subsequence, which need not coincide with the flat one. VD obtains alignment through its supercritical spanning argument. At the endpoint that argument may give only m−1 invariant directions and a nonplanar cone. Normalizing by the possibly much smaller mass of a flat-scale ball can destroy the uniform Frostman constant. No alignment lemma is proved here. The following attack grants the desired aligned endpoint data to test the next, independently necessary step; thus even solving this preliminary issue would not remove the error below.

The source already eliminates the zeroth-order reference-volume error. Translate S_i through a chosen density-Q center, use geodesic radius ρ on it, and weight the radial field by reciprocal geodesic volume density W. The identity

\[
 W(\operatorname{div}_S(\rho\nabla\rho)-m)
 +(\rho\nabla\rho)\cdot\nabla W=0
\]

is exact. After absorbing favorable normal terms, `eq:radial-almost-monotonicity` is

\[
 \dot I_i(X,t)\ge-C\varepsilon_i t^{1-m}
       \int_{\mathbf B_{Ct}(X)}(e_i+a_i^2)\,d\mu_i,
 \qquad\varepsilon_i\to0, \tag{A1}
\]

where dot is logarithmic-radius derivative. Averaging over σ_i and integrating **dt/t** gives, by Fubini,

\[
 \text{error}\le C\varepsilon_i a_i^2\int_0^l t^{s-m}\,dt.
 \tag{A2}
\]

For s>m−1 this is `Cε_i a_i² l^{s-m+1}/(s-m+1)=o(a_i²)` at each fixed l. The source first integrates from a positive cutoff to l, then sends the cutoff to zero **for each fixed i**, using the exact density-Q limit and Fatou; only afterwards does it let i→∞. Fixed-radius Taylor expansion and the centered first moment remove the translation cross term. This limiting order supplies V-center for all limiting centers.

At s=m−1, A2 is `ε_i a_i²∫_0^l dt/t`. The fact that ε_i→0 does not define this product. A diagonal cutoff ρ_i with `ε_i log(l/ρ_i)→0` controls only the truncated interval. It still needs density convergence `I_i(X,ρ_i)→Qc_Φ` with error `o(a_i²)` uniformly enough after averaging. Pointwise density at each fixed i supplies no such rate. Choosing ρ_i for density accuracy can make its logarithm arbitrarily larger than ε_i^{-1}.

A logarithmic Frostman gain `σ(B_t)≤Ct^{m−1}/log(e/t)^{1+δ}`, δ>0, would make that particular integral finite. It cannot be assumed for H^{m−1}-measure on the desired stratum: positive finite H^{m−1} subsets of a plane have order t^{m−1} at typical points. Nor does σ-finiteness of B follow from VD's dimension theorem. This proposed gain does not solve the stated endpoint target.

### Strong test: the limiting equations allow the forbidden concentration

It is tempting to claim that V-system automatically prevents tilt from charging an (m−1)-surface and hence restores A2. That claim is false **for this system alone**, even as a limit of smooth data.

Write `y=(y',x)∈R^{m−1}×R`, let `H={x=0}`, `e=e_m`, `P_H=Id−e⊗e`, and fix b>0. Define measures

\[
\begin{aligned}
 \nu&=(|x|+b)^2\,dy,&
 f&=(x+b\operatorname{sgn}x)e\,dy,\\
 \beta&=e\otimes e\,dy+\frac{2b}{m-1}P_H\,\mathcal H^{m-1}\!\llcorner H,&
 \mathfrak m&=\tfrac12dy.
\end{aligned} \tag{A3}
\]

These are locally finite on every bounded base domain. The absolutely continuous block matrix is rank-one PSD because `(x+b sgn x)²=(|x|+b)²`. The singular block has only the nonnegative β part. Distributionally `∇ν=2f`, `div f=dy+2b H^{m−1}|H=tr β`. The tangential constant matrix on H has zero divergence: integrating a tangential derivative against full hyperplane measure gives zero for compact tests. Hence `div β=0=∇𝔪`. Also `2𝔪=dy≤tr β` and `|𝔪|≤(tr β)/2`. Thus every V-system condition holds, with bounded height density, while the tilt has a codimension-one singular part.

Here is a smooth version, so the issue is not an artificial singular measure inserted without approximation. For η>0 put `r=(x²+η²)^{1/2}`, `w=r+b`, and take Lebesgue densities

\[
 \nu_\eta=w^2,\quad f_\eta=ww'e,
 \quad \beta_\eta=(w')^2e\otimes e+
       \frac{ww''}{m-1}P_H,\quad
 \mathfrak m_\eta=(w')^2-\tfrac12,
 \quad w'=x/r,\ w''=\eta^2/r^3. \tag{A4}
\]

The block is PSD: its normal 2×2 determinant vanishes and its tangential part is nonnegative. Direct differentiation gives the first two divergence identities. The third follows because only `∂_x(β_η)_{mm}` contributes and it equals `∂_x 𝔪_η`. Moreover

\[
 d_\eta=\operatorname{tr}\beta_\eta=1+b\eta^2/r^3\ge1,
 \quad d_\eta-2\mathfrak m_\eta
 =2\eta^2/r^2+b\eta^2/r^3\ge0,
 \quad|\mathfrak m_\eta|\le\tfrac12\le d_\eta/2.
\]

These data converge locally weakly to A3: `η²/r²→0` in L1_loc, whereas `η²/r³ dx⇀2δ_0`. Consequently, for σ equal to H^{m−1} on an interior disk of H, the part of the Fubini error from `Cη<t<c` is bounded **below** by `c_m b∫_{Cη}^c dt/t`. To see this, retain |x|≤η where the transverse mass is bounded below uniformly, and centers in an interior disk; each such strip point belongs to t-balls for a σ-set of order t^{m−1}. All tests have fixed interior room. With `ε_j=1/j` and `η_j=exp(−j²)`, multiplication by ε_j still diverges. Thus there is no uniform-integrability consequence of V-system that repairs the source estimate.

This is an obstruction to an inference, **not a stationary-varifold counterexample**. No claim is made that A4 is realizable by the source's actual normalized sheets. In fact A3 fails V-center at x∈H for small l, since its height average tends to a positive constant proportional to b² whereas its mass term is O(l²). That is exactly the logical point: invoking V-center to eliminate A3 would assume the estimate whose endpoint passage is in question. Centering of the original first height moment likewise cannot be replaced by an unproved harmonic-map representation.

**Attempt A outcome:** compensated averaging already uses the main obvious cancellation. One must gain a summable error from the actual integer sheets, or establish a density-convergence/tilt nonconcentration estimate before height normalization. The abstract limiting equations and ε_i→0 do not supply it. This is a precise obstruction, not a conditional rectifiability theorem.

## 7. Attempt B: quantitative frequency and translation splitting

Suppose, for this calculation only, that V-system and V-center have already been retained on a connected base region. This is the source's actual supercritical output; it is not asserted for endpoint centers. Put

\[
 H=\int\psi\,d\nu,\quad A=l^2\int\phi\,d\mathfrak m,
 \quad D=l^2\int\phi\,d(\operatorname{tr}\beta),
 \quad R_*=\int\psi\,d\beta[y-x,y-x].
\]

The source proves H>0 on every interior ball and

\[
 \dot A=2A-D+R_*,\quad \dot H=2D,
 \quad R_*H\ge D^2,\quad 2A\le D.
\]

Set `P=A/H`, `n_*=D/H`, `q_*=R_*/H`; V-center adds `P≥1/2`. Therefore

\[
 \dot P=2P-n_*+q_*-2Pn_*,\qquad n_*\ge2P\ge1.
\]

The following useful estimate remains valid at the borderline P=1/2:

\[
 \boxed{(q_*-n_*^2)+(n_*-2P)^2\le\dot P.} \tag{B1}
\]

Indeed subtract the left side from the exact right side: the remainder is `(2P−1)(n_*−2P)≥0`. Both terms on the left are nonnegative. Integrating B1 in log radius controls their total by the frequency drop. In particular there is no need to divide by `2P−1`; that would lose the linear-frequency endpoint.

There is a geometric version. Contract the positive matrix measure with `v_x(y)=(-2P(x,l),y-x)`. Then

\[
 \int\psi_{x,l}\,v_x^t\,d\mathcal M\,v_x
 =H[(q_*-n_*^2)+(n_*-2P)^2]
 \le H\dot P. \tag{B2}
\]

Take centers 0 and z with |z|≤l/4 and the same radius l. On `B_{l/4}(0)` both kernels have lower bound `c l^{-m}`. The difference of their contraction vectors is `(2(P_z−P_0),z)`. Positivity and `|a+b|_M²≤2|a|_M²+2|b|_M²` give

\[
 \int_{B_{l/4}}d\beta[z,z]
 \le C l^m(H_0\dot P_0+H_z\dot P_z)
       +8|P_z-P_0|^2\nu(B_{l/4}). \tag{B3}
\]

For finitely many centers whose position vectors span a k-plane with a fixed lower singular-value bound after scaling by l, elementary linear algebra turns these directional estimates into small β-energy along that plane. The conditioning constant must be retained. Integrating first in a fixed logarithmic annulus and selecting a common radius controls the sum of the finitely many frequency derivatives; one cannot select a different radius for every term in B3. Bounds on P on that annulus give height comparability by the source's `dot H/H=2n_*` and integrated q_* estimate. In the zero-drop, equal-frequency case B3 recovers the source's exact translation-annihilation argument.

This explains why a quantitative approach is plausible: frequency drops could pay for a best-plane error of the endpoint-center measure, leading to a square-function/packing argument. It also identifies what is still missing rather than calling B1 a solution:

- B3 controls β, not the Jones best-plane error of the **center measure**. A quantitative implication in the reverse geometric direction needs a nondegeneracy estimate and must relate height/stress directions to the distribution of centers.
- V-center is not established at endpoint centers. Attempt A shows why this cannot be supplied merely by the current abstract identities.
- The source's reference fits restart. Its `prop:target-frequency` gives bounded frequency and comparable heights on each prescribed-scale interval, not a single telescoping frequency for every center across all restarts with a summable transition error. B1 is an identity for one limiting tuple, not such a global function on the original singular set.
- Even restricting to an H^{m−1}-finite compact set only addresses that piece. The full target also needs a countable cover or σ-finiteness. No such conclusion follows from `dim_H≤m−1` alone.

These are separate requirements. B1–B3 are complete technical deductions from the source equations; they do not establish rectifiability and are not proposed as substantial findings.

Boundary checks: H=0 is excluded only using the source's no-open-zero-height lemma and `ν≠0`. The case P=1/2 is included in B1. Linearly dependent centers cannot control missing directions. Kernels require common interior room. A countable-density decomposition does not yield uniform constants in Q, but would be legitimate after a theorem for each Q; no global multiplicity bound is silently introduced. The m=1/countability problem is outside the selected target and the A3 construction, which divides by m−1.

## 8. Adversarial geometric test: a mass-only endpoint measure bound is false

A tempting strengthening of the target is a universal estimate

\[
 \mathcal H^{m-1}(\operatorname{Sing}V\cap B_1)
 \le C(m,n,\Lambda),\qquad \|V\|(B_2)\le\Lambda. \tag{false target}
\]

Already for m=2,n=1 this fails without a frequency/structural parameter. Here is a constructive proof, using actual smooth Euclidean minimal graphs rather than arbitrary harmonic graphs.

For each integer k≥2, prescribe boundary values `δ cos(kθ)` on the planar disk D_2. The minimal-surface operator from C^{2,α} functions to C^α is smooth near zero; its derivative with zero Dirichlet data is the invertible Dirichlet Laplacian. The implicit function theorem, after extending the boundary data smoothly, gives a unique small smooth minimal graph u_k for sufficiently small nonzero δ=δ_k. Choose δ_k still smaller so `||Du_k||∞≤1` and `||u_k||∞<1`. There is no claim of a lower bound for δ_k uniform in k.

For `θ_j=(2j+1)π/(2k)`, reflection across the diameter at angle θ_j changes the boundary values' sign. The minimal equation is invariant under domain reflections and u↦−u, and uniqueness of the small Dirichlet solution implies odd reflection of u_k. Hence u_k vanishes on k distinct diameters. It is not identically zero because the boundary values are nonzero. Interior analyticity of the scalar minimal graph implies it vanishes on no open disk.

Let `V_k=|graph u_k|+|graph(−u_k)|` in `U=D_2×(−2,2)`. Each graph has no boundary in U and is stationary; so is their sum. On the coincidence set the density is two, elsewhere one. Every coincidence point is singular in the full-support sense: if the support were one smooth embedded surface there, projection to the base would locally give one graph containing both graphs, forcing u_k=0 on an open set. The k diameters in the ambient unit ball therefore give

\[
 \mathcal H^1(\operatorname{Sing}V_k\cap B_1)\ge2k,
 \qquad \|V_k\|(B_2)\le8\sqrt2\pi.
\]

Both full sheets have bounded slope and even stable regular parts. The contradiction to a mass-only bound does not refute countable rectifiability; these particular nodal sets are analytic. Nor does it contradict quantitative-stratum bounds whose constants depend on ε or frequency: shrinking δ_k makes the sheets arbitrarily close to a double plane. The higher-dimensional product construction is possible but unnecessary for the stated rejection.

The smooth ambient examples of De Lellis–Hirsch–Lihn–Spolaor [2609.20647v1](https://arxiv.org/abs/2609.20647v1), Theorem 1.1, have a multiplicity-two planar tangent and infinite topology for m≥3, in a constructed **non-Euclidean** smooth metric. The earlier De Lellis–Hirsch–Spolaor [2509.21508v2](https://arxiv.org/abs/2509.21508v2), Theorems 1.1–1.2, use C^{1,α} metrics and include a stable-regular-part example with accumulating junctions. These show why planar tangents alone cannot be declared a multigraph in a broadened ambient category. They are not counterexamples to the Euclidean target, and no stability assertion is imported for arbitrary V.

## 9. Evidence, reproducibility, and handoff

Three fresh query batches, ten current arXiv metadata pages and ten corresponding versioned primary PDFs are retained with exact bytes, timestamps, final URLs and SHA-256 in [literature/manifest.json](../sources/i27_geometric_analysis_discovery/literature/manifest.json). [Primary read passages](../sources/i27_geometric_analysis_discovery/primary-read-passages.json) and [version histories](../sources/i27_geometric_analysis_discovery/primary-versions.json) record the actual comparisons. The versions are NV v4 (2017-07-28), CCL v3 (2022-02-05), HS graphs v1 (2023-12-30), Martens v2 (2025-04-22), Liu–Simon v2 (2025-03-28), BDLF v1 (2025-03-01), DLHS v2 (2026-04-12), KMW v1 (2026-06-01), Kolasiński v1 (2026-09-17), and DLHLS v1 (2026-09-17). A current search is bounded evidence, not worldwide-priority certification. Bibliographic metadata is not used as a substitute for theorem hypotheses.

The deterministic diagnostics check 6,612 rational frequency cases, 15,444 distributional-model algebra cases, 10,416 smooth stress approximants, 199 normalized product metrics, 80 scalar-spike scalings, 49 PSD subtraction cases, 20,300 exact reflection phase identities, and 39 endpoint cutoff sequences. The report supplies the general algebraic, distributional and PDE arguments. Finite checks do not prove geometric realizability of A4 or solve the target. No numerical minimal-surface solution is passed off as an existence proof.

From the project root:

```sh
python frontier/experiments/i27_geometric_analysis_discovery/diagnostics.py
python frontier/experiments/i27_geometric_analysis_discovery/contracts.py
python frontier/experiments/i27_geometric_analysis_discovery/verify.py
python frontier/experiments/i27_geometric_analysis_discovery/seal.py --verify
```

`fetch_primary.py` performs fresh network requests and changes timestamped evidence; it is not a retained-byte verification command. The seal covers the report and all designated artifacts except its own manifest and derived verification outputs. The initial verification passes for 9 frozen inputs, 96 selected pinned files, 209 statement blocks, 25 source read passages, 10 primary read passages, 20 primary retrievals and the full 9,340-file cache. Only shared-ledger drift was observed: TEN-FINDINGS changed from `276b3259005a8cab1716815a7e5150cb6dc3961c70e366e7e736319934de7401` to `0a1144320c5f861d07886dee34a3f5c748ed0369f73da17ead3aaf1db6517a38`; the frozen copy controls this report. The verifier reports subsequent live shared-index drift separately from changes to frozen mathematical premises. No shared index, commit, staging area, public repository, or other project was changed by this task, and no further agents were started.

**Handoff:** the full Euclidean endpoint rectifiability target remains unproved. A follow-up should attack alignment of flat scales with endpoint center mass, actual-sheet endpoint density/tilt control, or a restart-compatible quantitative center frequency, with KMW's stronger ε-regularity hypothesis kept explicit. Merely assuming one of those missing estimates, applying NV to the already-covered classical stratum, or promoting B1–B3/A3/the product example into separate findings would misstate this result.
