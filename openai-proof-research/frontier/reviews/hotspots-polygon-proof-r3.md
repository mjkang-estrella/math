# Independent adversarial proof review: polygonal hot spots, round 3

Date: 2026-10-08. Candidate: `hotspots-multiplicity-r2.md`, Sections 2–6. Prior review: `hotspots-review-r2.md`. Repository instructions and source contracts were read. The pinned OpenAI corpus at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is accepted as true; its proofs are not being audited. This review independently checks the new deductions.

**Parent integration:** accepted as technical finding [R003](../findings/R003-polygon-eigenline-selection.md). The parent verified all nine successful source hashes and reproduced both exact-check outputs. The [separate novelty review](hotspots-polygon-novelty-r3.md) has now identified the smooth cross-stress mechanism and polarization in published work; it classifies the polygon extension as modest, with priority unconfirmed. This resolves the pending novelty comparison below without treating the user’s research objective as complete.

## Verdict and exact scope

**Accept the mathematics of Sections 2–6, with the technical clarifications below. I found no fatal gap or counterexample.** In particular, the reentrant-corner argument survives differentiation, infinite-tail estimates, and the angle `3π/2`. The shape argument gives the required *prescribed lower eigenline*, not merely some splitting direction. The actual Ball–Zarnescu statement supports the smoothing contract used here.

The verified assertions are:

1. On every bounded simply connected planar Lipschitz domain, the real first-positive Neumann eigenspace has dimension at most two. The full-support measure proof is valid without classical boundary derivatives.
2. On every bounded connected polygonal **Lipschitz** planar domain, possibly with holes, no pair of nonzero real Neumann eigenfunctions at a common positive eigenvalue satisfies `h_τ k_τ = λhk` on every open side. This includes higher eigenvalues and dependent pairs.
3. At a double positive polygonal eigenvalue, the map from smooth ambient fields vanishing near the vertices to traceless symmetric shape forms is onto. If the eigenvalue is the first positive one, any prescribed eigenline is the simple lower branch for an appropriate deformation with `t>0`.
4. Every first-positive eigenfunction of a bounded simply connected polygonal Lipschitz domain is a local smooth limit of first-positive eigenfunctions on smooth simply connected domains. The approximating first-positive eigenvalues can be simple.
5. **Conditional on family 369**, every such polygon and every nonzero real first-positive eigenfunction satisfy

   `min_{∂P} u < u(x) < max_{∂P} u` for every `x∈P`.

Assertions 1–4 do not need the accepted hot-spots theorem. Assertion 5 does. Neither the argument nor these checks prove general Lipschitz eigenline selection, gradient nonvanishing on polygons, or a nested smooth exhaustion inside the original polygon. “Polygon” must exclude slit tips, self-touching boundaries, and zero-width necks.

**Novelty verdict:** this closes a genuine gap in the earlier simple-eigenvalue transfer, through a substantive corner/transversality argument. It should not be dismissed *solely* as another application of spectral convergence. Nevertheless, this proof review establishes neither external priority nor the user's requested level of research significance. Retain it as a mathematically verified technical advance within the project, pending a separate primary-literature novelty comparison. Lemma R and smoothing remain classical; they must not be repackaged as the new contribution.

## 1. Primary-source contracts checked

Fresh source downloads, hashes, and input-file hashes are in [the manifest](../sources/hotspots_polygon_proof_r3/manifest.json). PDFs were extracted to text and the actual statements below were read. A failed guessed erratum URL is recorded; the erratum was subsequently retrieved successfully from its versioned arXiv URL.

- **OpenAI family 369:** [pinned `01-introduction.tex`, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/build/sections/01-introduction.tex) assumes bounded nonempty simply connected planar domain with `C∞` boundary and covers every nonzero first-positive eigenfunction, including multiplicity. The preliminaries' multiplicity proposition has the same smooth standing hypothesis. The introduction and conclusion do not already state the polygonal transfer proved here. The catalogue and preprint-path listing identify this family; catalogue wording was not substituted for its theorem.
- **Nittka:** [arXiv:0906.5285, Theorem 3.14(ii)](https://arxiv.org/pdf/0906.5285), PDF p. 11, applies on Lipschitz domains. Set `N=2`, `q=1`, `ε=1`, `f₀=λu∈L²`, and the remaining data zero. The conclusion is Hölder continuity on the closure. Uniqueness of the inhomogeneous problem is not required for part (ii); it would only be needed to remove the `‖u‖₂` term in the stronger estimate. This supports continuous pointwise boundary traces, not smooth boundary gradients.
- **Judge–Mondal:** [2020 journal paper, Section 4, (5), (6), (10)](https://annals.math.princeton.edu/wp-content/uploads/annals-v191-n1-p03-s.pdf) gives the sector expansion and radial differentiation without an outer-arc boundary condition. Section 5 begins with a simply connected polygon; Corollary 5.4 states multiplicity at most two in that setting. Its expansion citation alone does not state the precise uniform differentiated remainder needed here; §3 below supplies that estimate directly. The [erratum, arXiv:1802.01800v5, introduction](https://arxiv.org/pdf/1802.01800v5) identifies the defective Lemma 3.4 and affected results. This review uses neither that lemma nor the affected triangle hot-spots proof. The sector expansion is independently justified below, and the polygonal multiplicity assertion is independently covered by §2.
- **Ball–Zarnescu:** [arXiv:1312.5156v3, Theorem 5.1(ii) and Remark 5.3](https://arxiv.org/pdf/1312.5156v3), PDF pp. 11 and 18, provide the same approximation family and maps used in the candidate: inner domains `D_ε={ρ>ε}`, ambient homeomorphisms of closures, identity wherever `|ρ|>3|ε|`, and, for Lipschitz `D`, bi-Lipschitz constants independent of small `ε`. The independence is for a **fixed domain D**. It is not a uniform bound over all polygons or all degenerating corner angles. The proof needs only the fixed-domain assertion.
- **Bérard–Helffer:** [2021, Lemma 4.3 and Remark 4.4, p. 456](https://www.numdam.org/item/AFST_2021_6_30_3_429_0.pdf) give the earlier shifted-eigenfunction nodal-component result implying Lemma R. Choosing the second basis eigenfunction to be a specified normalized first-positive eigenfunction is legitimate even at multiplicity. The previously identified priority objection remains.
- **Hillairet–Judge:** [arXiv:math/0703616, Theorem 1.1](https://arxiv.org/pdf/math/0703616) states simple Dirichlet/Neumann spectrum for almost every simple polygon with a fixed number `n≥4` of vertices. It does not assert local control of every prescribed lower eigenline at an arbitrary polygon. Generic simplicity is not a replacement for candidate Sections 3–5.

## 2. Lipschitz multiplicity: independent logical audit

Write `μ=μ₁ᴺ(Ω)` and `λ_D=λ₁ᴰ(Ω)`. All compactness and trace statements below apply to bounded Lipschitz domains.

**The strict gap is justified.** If `φ∈H¹₀(Ω)` is a nonnegative Dirichlet ground state and `|k|²=λ_D`, the quadratic form `Q(v)=∫(|∇v|²−λ_D|v|²)` vanishes on `e^{ik·x}` and on `φ`. The cross term vanishes by testing the *plane wave's* distributional equation against `φ`; no normal derivative of `φ` is used. Subtracting a multiple of `φ` makes the wave mean zero. Thus `μ≤λ_D`. Equality would place an infinite-dimensional span of such mean-zero waves in a finite-dimensional eigenspace. Linear independence follows by restricting any finite collection to a generic line segment in an interior ball; subtracting multiples of one fixed vector removes at most one dimension. This proves strictness in the stated planar setting. The temporary complexification is harmless.

**Every nonzero trace changes sign.** If the continuous trace of `u∈E` is nonnegative, its negative part has zero Sobolev trace and lies in `H¹₀(Ω)`. The weak eigenfunction equation gives its energy equal to `μ` times its squared norm. The Dirichlet gap forces it to vanish. Zero mean then forces `u=0`. Repeating for `−u` proves the claim and, in particular, injectivity of the trace on `E`.

**Full support is correctly constructed.** For the trace-evaluation vector `U:S¹→R^m`, failure of `0∈int conv U(S¹)` gives a nonzero separating functional that is nonnegative on every trace vector, including the case where the convex hull has deficient affine dimension. This contradicts the preceding sign result. The convex hull is compact in finite dimension. Adding a sufficiently small positive multiple of circle measure and compensating its barycenter by a finite convex combination therefore gives the asserted positive probability measure annihilating all traces. Its atomic part presents no problem: the trace functions are continuous, and the absolutely continuous summand gives full support. No conformal-map derivative or boundary Hopf lemma is implicit in this step.

**Nodal topology is sufficient at multiplicity.** A restriction `u1_C` to a sign component is locally Lipschitz across its interior zero interface, has weak gradient `1_C∇u`, and lies globally in `H¹`. If three sign components existed, a mean-zero combination of two such restrictions would attain the first-positive Rayleigh quotient but vanish on the third. Its weak Euler equation holds against all `H¹` tests, and analyticity contradicts its open zero set. This avoids misapplying a version of Courant's theorem indexed by the *last* position in a repeated eigenvalue cluster.

A bounded simply connected planar Lipschitz domain is a Jordan domain. At a strictly positive boundary value, continuity and a local graph chart give a short positive interior access arc; the negative case is identical. Connected open sign sets are path connected, and loops can be removed. Alternating signs at four boundary points would force the two resulting disjoint-sign crosscuts to intersect. No boundary nodal expansion is needed.

Finally, if `dim E≥3`, impose the two cosine/sine orthogonalities. The constant orthogonality is supplied by the measure, not counted as a third independent constraint. After cutting at a negative point, the candidate's `a,b` obey `θ₀<a<b<θ₀+2π`. Nonalternation excludes negative values between `a,b`. The displayed first-harmonic test has the same weak sign as the trace and is strictly aligned on a nonempty open interval. Its positive integral contradicts the three orthogonalities. This verifies the full Lipschitz multiplicity claim.

The bound is first-positive and topological. It does not apply to arbitrary higher eigenvalues or multiply connected domains.

## 3. Statement P: rigorous sector remainder and corner audit

### 3.1 Why the expansion and its derivative are available

Fix a vertex and a sector `0<r<R`, `0<θ<β` lying exactly in the polygon. Set `ν=π/β`, `κ=√λ`, and reduce `R` so `κR≤1`. Angular cosine expansion of a weak `H¹` Neumann solution gives radial Bessel equations with orders `nν`. The irregular solutions are excluded by finite energy: `Y₀` has logarithmic derivative of order `r⁻¹`, and for positive order the irregular solution has a negative-power singularity with nonintegrable gradient energy. Thus only `J_{nν}(κr)` occurs. This argument works for reentrant sectors; no convexity enters.

Choose the outer radius inside a larger valid sector. The trace on this circular arc is in `L²(0,β)` (indeed it is smooth, using reflection at its endpoints away from the vertex). Let its cosine coefficients be `g_n`, so `Σ|g_n|²<∞`. The expansion can be written

`u(r,θ)=Σ_{n≥0} g_n [J_{nν}(κr)/J_{nν}(κR)] cos(nνθ)`.

For clarity, use the standard normalized Bessel power series, for `α≥0`,

`J_α(κr)=(κr/2)^α/Γ(α+1) · S_α(r)`,

`S_α(r)=Σ_{j≥0} (−λr²/4)^j/[j!(α+1)_j]`.

Uniformly in `α≥0` and `r≤R`,

`|S_α(r)−1|≤exp(λr²/4)−1<1/2`,

`|r S'_α(r)|≤2(λr²/4)exp(λr²/4)`.

In particular the denominators at `R` are nonzero. The ratios are bounded by `C(r/R)^α`, and for `α>0` their radial derivatives are bounded by

`C(α+1)r⁻¹(r/R)^α`.

The `α=0` ratio instead has derivative `O(r)`. Constants can depend on the fixed sector and radius; that is sufficient.

For `r≤R/2`, Cauchy–Schwarz applied to `g_n` and the geometric factors gives, for every fixed `N≥1`,

`sup_θ |Σ_{n≥N} g_n J_{nν}(κr)/J_{nν}(κR) cos(nνθ)| ≤ C_N r^{Nν}`,

`sup_θ |Σ_{n≥N} g_n ∂_r[J_{nν}(κr)/J_{nν}(κR)] cos(nνθ)| ≤ C_N r^{Nν−1}`.

The bounds on compact annular subsectors justify termwise differentiation; the estimates then hold uniformly all the way to both rays. They also establish the continuous vertex value. Taking `N=3`, and separately expanding the first three Bessel factors, proves exactly (3.1)–(3.2). The radial zeroth-mode correction is `O(r²)` with derivative `O(r)`; first- and second-mode corrections have powers `ν+2` and `2ν+2`, which are absorbed in the displayed remainders.

**Editorial correction:** uniform convergence of the undifferentiated series away from the vertex does not, by itself, imply the differentiated estimate at the vertex. Include this ratio/tail argument, or an equivalent explicit estimate, when promoting the proof. There are no extra logarithms at `ν=2/3`: the homogeneous separated Bessel equations have already excluded the irregular branches. Rational coincidences between exponents do not create logarithmic solutions here.

### 3.2 Convex and reentrant corners

For `β<π`, `ν>1`, so each side derivative tends to zero. Since `h→A` and `k→B`, the assumed identity forces `λAB=0`.

For `π<β<2π`, use the candidate's notation

`h'_s=sνa r^{ν−1}+2νb r^{2ν−1}+R_s`,

`k'_s=sνc r^{ν−1}+2νd r^{2ν−1}+T_s`,

with `s=±1` and `R_s,T_s=O(r^{3ν−1}+r)`. Boundedness of `λh_sk_s`, followed by multiplication by `r^{2−2ν}`, forces `ac=0`. All other derivative-product powers are strictly higher than `2ν−2`, even when they themselves diverge before rescaling.

The two-edge average is

`ν²ac r^{2ν−2}+4ν²bd r^{4ν−2}+E(r)`.

The displayed leading/second-mode mixed product changes sign exactly. An explicit sufficient error bound is

`E=O(r^{4ν−2}+r^ν+r^{5ν−2}+r^{2ν}+r^{6ν−2}+r^{3ν}+r²)`.

Every exponent in this error bound is positive for `ν>1/2`. Hence, after `ac=0`, the average tends to zero. The right-hand average tends to `λAB`, giving `AB=0`.

This also clarifies the candidate's `+4ν²bd r^{4ν−2}+o(1)`: it is a valid limit statement, but **not** a complete expansion through order `r^{4ν−2}`. Products of the first and third angular modes can contribute at that same order. They are absorbed by `o(1)`, which is all that the proof needs.

At `β=3π/2`, `ν=2/3`, the leading mixed term is constant on each side and has opposite signs. For `β>3π/2` it diverges on each side but cancels just as exactly. No single-edge argument may discard it. More generally, averaging removes odd `n+m`; among even positive-mode sums only `(n,m)=(1,1)` can fail to decay for `ν>1/2`. Corrections of positive radial order decay. This is the conceptual explanation of the calculation.

### 3.3 The excluded endpoint is real, not cosmetic

A polygonal Lipschitz graph has two distinct boundary rays with angle strictly between `0` and `2π`. A `2π` tip would require a slit with the domain on both sides; it is not a Lipschitz-domain boundary chart. Delete artificial straight-angle vertices before applying the corner conclusion: at `β=π`, side derivatives need not vanish, and the asserted vertex-product conclusion is not available.

At the excluded angle `2π`, the second angular mode has degree one and the surviving `(2,2)` derivative product has exponent zero. There is an explicit local obstruction to extending the corner lemma. On a disk slit along the positive x-axis, take

`h=k=exp(√λ x) cos(√(2λ) y)`.

It solves `−Δh=λh`, has zero normal derivative on both slit faces, belongs to local `H¹`, and on each face satisfies `h_τ k_τ=λhk`, with `h(0)k(0)=1`. No condition is imposed on the circular arc. This is a counterexample to the **local vertex-product conclusion at angle 2π**, not a counterexample on a bounded polygonal Lipschitz Neumann domain.

For each fixed angle below `2π`, the argument remains valid. It is nonuniform as the angle tends to `2π`: `4ν−2→0+`, and neither the sector constants nor subsequent deformation-control constants were proved uniformly bounded. Near-slits do not refute the fixed-polygon theorem, but they forbid using this proof as an unqualified slit-limit argument.

### 3.4 From local corners to a contradiction on the polygon

On an open side, a nonzero stationary value of `w=hk` would have `h,k≠0` and logarithmic derivatives satisfying simultaneously `a+b=0` and `ab=λ>0`, impossible over the reals. Real-valuedness and positivity of `λ` matter.

Every closed side has zero endpoint values of `w`. If `w` were nonzero somewhere on it, continuity would give an interior nonzero maximum or minimum, which the preceding calculation forbids. Thus `hk=0` on each whole side.

To finish, even reflection across a straight open side extends each weak Neumann eigenfunction to a weak Helmholtz solution in a full neighborhood, hence to an analytic function. If a trace vanished on an open subinterval, both Cauchy data would vanish. One can verify uniqueness directly: all tangential derivatives vanish, the Neumann data annihilate the first normal derivatives, and the equation recursively annihilates all higher normal derivatives. Analyticity then gives an open zero set and connectedness propagates zero throughout the domain.

Consequently `h` is nonzero on some subinterval of any side; there `k=0`, and the same uniqueness forces `k≡0`. This proves P. Holes do not affect this sidewise contradiction. At `λ=0`, nonzero constants violate P's conclusion, and on disconnected domains disjointly supported eigenfunctions do so; those hypotheses cannot be dropped.

## 4. Shape forms: no hidden corner integration

For `V∈C_c∞(R²;R²)` vanishing in neighborhoods of all vertices, `Φ_t=Id+tV` is a global diffeomorphism for sufficiently small `|t|`. Pullback gives forms on the fixed space `H¹(P)` with uniform ellipticity and Taylor expansions in form norm. Differentiating the inverse Jacobian and determinant gives (4.1), including its minus sign in front of `DV+DVᵀ` and the mass contribution `−λ div(V) vz`.

For eigenfunctions `v,z`, define the symmetric stress tensor

`T=(∇v·∇z−λvz)I−∇v⊗∇z−∇z⊗∇v`.

Its divergence is zero by `Δv=−λv`, `Δz=−λz`. On a straight Neumann side, `Tn=(v_τz_τ−λvz)n`. Integrating `T:DV` gives (4.2). This integration can be done after removing small corner neighborhoods on which **V is identically zero**. Their artificial boundaries have zero flux contribution. Thus no nonexistent `H²` corner regularity, corner trace of the gradient, or omitted vertex term is used. Interior-supported fields also yield zero, as required by invariance under a reparametrization that fixes the domain.

A scalar bump normal speed on a compact subinterval of an open side extends to an allowed ambient field by a tubular cutoff. These independent local tests justify pointwise vanishing of a smooth side density from the integral identities.

If the traceless image were proper, its finite-dimensional orthogonal complement would contain a nonzero traceless symmetric matrix. In an orthonormal eigenbasis of that matrix it is `diag(ρ,−ρ)`. Annihilation says `q(f,f)=q(g,g)` for all fields. The local side identities factor with `h=f+g`, `k=f−g`, yielding P. Both functions are nonzero, and P gives the contradiction. This proves surjectivity.

The allowed deformed domains usually have **curved** sides; they are not constrained to remain polygons, rectangles, convex domains, or symmetric domains. The theorem does not need any such constraint. The exact double-eigenspace hypothesis is needed for the next lower-branch assertion. Pairwise results inside a higher-dimensional eigenspace do not establish controllability of the whole cluster.

## 5. Selection, spectral gap, and smoothing

### 5.1 Prescribed line is the lower branch

For unit `u∈E(P)`, choose a unit perpendicular `v`. Surjectivity allows a field whose traceless shape matrix is `diag(−1,1)` in this basis. Consequently the full matrix has eigenvalues `α<β` with lower eigenline `Ru`, regardless of its scalar part.

Let the positive eigenvalues be `μ₁≤μ₂≤μ₃≤…`. At the original polygon, `μ₁=μ₂=μ<μ₃`. Form-norm comparability and the min–max principle, including the constant zero eigenspace, give `μ_j(t)=μ_j(0)+O(t)` for each fixed index. In particular the two-dimensional cluster remains isolated from both zero and `μ₃`.

For a normalized first eigenfunction pulled back to `v_t`, compactness gives a normalized mean-zero limit in `E(P)`. The limiting equation is valid for all `H¹` tests. Its energy equals `μ`, so weak `H¹` convergence upgrades to strong `H¹`. Expanding the weak equation against `z∈E(P)` then gives exactly the candidate's equation

`[(μ₁(t)−μ)/t] b₀(v_t,z)=q_V(v_t,z)+o(1)`.

The identity `a₀(v_t,z)=μb₀(v_t,z)` is valid despite the perturbed mean of `v_t`, since `z` satisfies the original weak Neumann equation against **all** `H¹` functions.

Mean-adjusting the fixed trial vector `u` changes its mass by

`−b_t(u,1)²/b_t(1,1)=O(t²)`

and does not change its energy. Its quotient is `μ+tα+O(t²)`. For `t>0`, the first eigenvalue therefore has derivative at most `α`. Every subsequential derivative is an eigenvalue of `q_V`, so it must equal `α`; every subsequential eigenfunction limit lies in `Ru`. Sign selection gives convergence to `u`. The restriction `t>0` is essential: the ordering reverses with the sign of `t`.

The candidate's simplicity proof is valid. If arbitrarily small positive `t` had two orthonormal minimizing eigenfunctions, both would converge along a subsequence to unit vectors on `Ru`, while their pulled-back `b_t` inner product converges to the usual inner product zero. This is impossible.

For an explicit gap check, choose a normalized second positive eigenfunction orthogonal to the first. Min–max bounds keep it in the isolated cluster with `μ₂(t)=μ+O(t)`. Its limit lies in `E(P)∩u^⊥`, so the same first-order equation gives derivative `β`. Therefore

`μ₁(t)=μ+αt+o(t)`, `μ₂(t)=μ+βt+o(t)`,

`μ₂(t)−μ₁(t)=(β−α)t+o(t)>0`.

This explicitly rules out a hidden unsplit competitor for the first-positive branch. The gap to the rest of the spectrum remains positive. There is no appeal to generic simplicity in this reasoning.

Pullback convergence also implies physical local `L²` convergence: on a fixed compact interior set, composition with `Φ_t⁻¹→Id` preserves the vanishing error by bounded Jacobians, and composition of the fixed smooth limiting function converges to itself. Interior elliptic estimates then give `C∞_loc` convergence. Eventual inclusion of every interior compact follows from `Φ_t→Id` uniformly and invertibility.

### 5.2 Exact smoothing contract suffices

Fix a small `t>0` first, and put `D=P_t`. It is bounded, Lipschitz, and simply connected, with simple first positive eigenvalue. Ball–Zarnescu provides inner smooth `D_ε` and maps `F_ε:D→D_ε`. For every compact `K⊂D`, `F_ε=Id` on a neighborhood of `K` for all sufficiently small `ε`. The same fixed-domain family has uniform Lipschitz constants for the maps and their inverses.

The change-of-variables formula and Sobolev composition for bi-Lipschitz maps make pullbacks of normalized first eigenfunctions uniformly bounded in `H¹(D)`. Their Jacobians satisfy `0<c≤J_ε≤C`. Moreover, for almost every fixed interior point they are eventually one; on every fixed compact set they are one almost everywhere for all small `ε`.

If `z_ε→z` strongly in `L²(D)`, then `z_ε²→z²` in `L¹`. Thus

`∫z_ε²J_ε→∫z²`, `∫z_εJ_ε→∫z`,

by the uniform Jacobian bounds and dominated convergence for the fixed limits. This is enough to preserve normalization and zero mean. One must not replace strong convergence by mere weak convergence in this step.

The restriction/mean-correction trial function gives the upper eigenvalue bound because the omitted inner collar shrinks to the boundary. On compact interior subsets the maps are exactly identity, so energy lower semicontinuity followed by exhaustion gives the matching lower bound and a normalized minimizing limit. No global convergence of `DF_ε` to the identity, and no uniform corner `H²` estimate, is assumed. Local elliptic regularity gives physical `C∞` convergence.

Simplicity of the fixed limit domain selects the desired eigenfunction after fixing signs. The same two-orthonormal-limits argument proves eventual simplicity of the smooth approximants. Their weighted inner products converge by strong `L²` compactness and the Jacobian bounds just checked.

Finally choose `t_j→0+`, and **then** choose `ε_j` separately for each `t_j`, small enough to obtain the desired accuracy and compact inclusion. Constants may depend on `t_j`; no uniform approximation rate or inverse-control norm is needed for this diagonal choice. One can additionally impose `ε_j<1/j` and any desired fixed-index geometric closeness. A preassigned common smoothing rate has not been justified and is unnecessary.

This proves `L(P)=E(P)` with the scout's actual definition: eventual inclusion of each compact and local uniform eigenfunction convergence on smooth simply connected approximating domains. It does not require the final domains to be nested or contained in `P`. Unit normalization only selects a representative; scaling the approximants covers every real eigenfunction, and zero causes no issue.

## 6. Hot-spots transfer and maximum-set topology

The accepted smooth theorem makes all approximating gradients nonzero. A strict interior local maximum or minimum of the limit supplies a closed ball with a positive value gap on its boundary. Uniform convergence would give an interior extremum of every sufficiently close approximant. Thus strict local extrema are excluded. Local degree stability similarly excludes every isolated critical point with nonzero vector-field index, and hence every critical point with invertible Hessian. It does not exclude degenerate index-zero critical points.

For a global maximum `M`, zero mean ensures `M>0`. The component cutoffs `f_C=(u−M)1_C` belong to `H¹` by the same local zero-interface argument as in §2. The identity

`μ‖f_C‖²−‖∇f_C‖²=μM∫_C(M−u)>0`

has the correct sign. Two components would yield a mean-zero trial function of quotient below `μ`. Thus `P\{u=M}` is connected. This is the classical Lemma R step, not a new novelty claim.

At a maximum, the Hessian is negative semidefinite with trace `−μM<0`. In dimension two its rank is one or two. Rank two makes the maximum isolated. For rank one, solve the transverse derivative equation by the analytic implicit function theorem. The remaining equality to `M` is the zero set of a one-variable analytic function, which is either isolated or identically zero locally. Thus the maximum set is locally an isolated point or a single embedded analytic arc. An isolated maximum is strict, including the degenerate case, and has already been excluded.

It follows that any nonempty maximum set is a relatively closed embedded one-manifold without boundary in `P`. Each connected component is closed in `P`, with its subspace topology, and is therefore properly embedded. It is a circle or a line. Under a homeomorphism `P≅R²`, a circle separates, and a proper line separates by extending it to a Jordan circle in the one-point compactification. This does not assume distinct Euclidean endpoints on `∂P`.

The maximum set has empty interior by analyticity. Hence each side of the separating component has a point outside the full maximum set. No path in the complement can join these points, contradicting its connectedness. This proves absence of attained interior global maxima; apply it to `−u` for minima. Boundary continuity and compactness then yield the strict boundary inequalities, not merely existence of boundary maximizers.

## 7. Adversarial examples and reproducible checks

The [independent exact-check script](../experiments/hotspots_polygon_proof_r3/check_exact.py) uses only integer and rational arithmetic. It copies the original round-2 corner script into this review's directory before executing it, so the rerun does not overwrite the original result. Outputs are [the original-check rerun](../experiments/hotspots_polygon_proof_r3/original_corner_results.json) and [the independent results](../experiments/hotspots_polygon_proof_r3/results.json).

- The original 144 parity-pair tests passed. The independent tests include 7,830 surviving derivative products from angular modes `0,…,12` and radial corrections `0,…,3`, at six rational values of `ν`, including `2/3` and `500001/1000000`. They check derivative-zero constants, radial-mode corrections, odd-parity cancellation, and positivity of all remaining exponents except the forced-zero `(1,1)` coefficient. The infinite-mode statement follows from §3.1, not from finite enumeration.
- On the square `(0,π)²`, `E₁=span{cos x,cos y}`. For `h=cos x+cos y`, `k=cos x−cos y`, the product vanishes at every vertex, so vertex vanishing alone is not a contradiction. On `y=0`, however, `h_τk_τ−hk=1−cos(2x)=2sin²x`, so P fails as required. The side traceless densities for the basis `cos x,cos y` are proportional to `2sin²x` and `−cos x`; these are independent. Local side bumps can therefore rotate the lower line. Varying only rectangle side lengths would not have this freedom.
- For the repeated higher eigenvalue `λ=5`, take `f=cos x cos(2y)` and `g=cos(2x) cos y`. Again `h=f+g`, `k=f−g` make all corner products zero. On `y=0`, the stress is `−3/2−3cos(2x)+(9/2)cos(4x)`, which is not identically zero. More generally 2,840 exact basis-pair and deterministic integer-mixture tests over three rational rectangle aspect ratios and eigenvalues up to 100 found no violation, including eigenspaces of dimension four. These tests do not prove surjectivity on four-dimensional clusters; no such claim is made.
- Near-slit checks give the slow but positive exponent `4ν−2=1/250000` at `ν=500001/1000000`. The explicit `2π` local solution in §3.3 confirms exactly where the corner proof stops. Thin-neck or near-touching families can also lose uniform spectral gaps and geometric constants, but each fixed nondegenerate polygon is covered.

No finite-element eigenvalue estimates were used as proof evidence. The PDE, compactness, Cauchy uniqueness, and topology arguments were checked separately above.

## 8. Required presentation corrections and disposition

1. Retain “bounded connected polygonal Lipschitz domain,” real eigenfunctions, and positive common eigenvalue in P. Retain simple connectivity and first-positive indexing in the final hot-spots theorem. Delete redundant straight vertices; do not silently include slit polygons.
2. Promote the differentiated Bessel-tail estimate to an explicit lemma. Describe the average as a limit estimate; do not claim its displayed second term is the entire coefficient of `r^{4ν−2}`.
3. State that shape fields may curve the sides, and that lower selection uses `t>0`. The isolated two-dimensional cluster and the gap calculation in §5.1 make the branch argument fully reviewable.
4. Quote the identity-off-collar property and uniform bi-Lipschitz property from the **same** Ball–Zarnescu family. Fix the selected domain before smoothing; choose the diagonal smoothing scales afterwards. Uniformity across a degenerating family was not proved.
5. Keep the planar proper-maximum-set argument and the distinction between strict hot-spots inequalities and nonvanishing gradient. Keep arbitrary Lipschitz selection explicitly unresolved.
6. Attribute Lemma R and classical smoothing as before. The additional result now verified is polygonal cross-stress exclusion and its prescribed-eigenline consequence. Neither a bounded search nor this proof verification establishes that this mechanism is absent from the shape-perturbation literature. Do not label the user's novelty/significance objective complete on this evidence alone.

**Final disposition:** mathematically accept the polygonal theorem conditional on family 369, with the clarifications supplied here; accept Statement P and the eigenline-selection theorem independently of family 369. This supersedes the prior review's multiplicity-gap objection for polygons, but not for arbitrary Lipschitz domains. External priority and qualification as a significant new MathDB advance remain unestablished.

Only this report and `frontier/{sources,experiments}/hotspots_polygon_proof_r3/` were written. No staging, commits, shared-file edits, or nested agents were used.
