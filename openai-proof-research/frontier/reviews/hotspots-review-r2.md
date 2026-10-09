# Independent adversarial review: nonsmooth hot-spots extension, round 2

Date: 2026-10-08. Reviewed `frontier/scouts/analysis.md`, especially Lemmas R, T, A and Theorem H(a)–(e). The pinned `openai/math` corpus at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is accepted as true; this review checks its source contract and the new deductions, not its proofs. No shared files were edited and no agents were delegated.

## Verdict

**Mathematical verdict: H(a)–(e) is valid after the repairs and clarifications below. I found no unrepairable mathematical gap in those conclusions.** The maximum-set topology and the component cutoffs withstand scrutiny. The omitted convergence justification in H(c) is short and follows from the existing definition of L; that definition need not be strengthened. Precise, independently checked references supply the approximation and boundary-continuity inputs.

**Research-selection verdict: reject this as satisfying the user's request for a genuinely novel proof idea, as presently proposed.** The advertised new Lemma R is a special case of a published stronger result: Bérard–Helffer (2021), **Lemma 4.3 and Remark 4.4**, p. 456, with the Courant-type mechanism attributed to Gladwell–Zhu (2003), **Theorem 1**, pp. 279–280. Spectral approximation is likewise classical, down to substantially the same extension/compactness proof: Ni–Wang (2007), **Proposition 5.4**, pp. 16–18. The remaining analytic-arc/Jordan argument is a useful elementary closure argument, but does not establish a new proof mechanism of the requested significance.

The precise Lipschitz corollary is not stated in the upstream manuscript I checked, and I did not find an exact pre-existing published statement of the entire conditional extension. That supports retaining it as a **conditional regularity-transfer corollary, new to this project**, not declaring a new-to-literature advance or a newly discovered separation lemma. This novelty verdict is separate from the mathematical acceptance.

## 1. Mandatory corrections

1. **Introduction overstates the domain class.** “That class includes every simply connected polygon ... and every bounded convex planar domain” is false for the class with simple first positive eigenvalue. On `(0,π)^2`, the first positive eigenvalue is 1 and its eigenspace is spanned by `cos x` and `cos y`. A square is both a simply connected polygon and convex. Say instead: “This applies to every such polygon or convex planar domain **whose first positive eigenvalue is simple**. Without simplicity it proves existence of at least one favorable eigenfunction.” A polygon here should mean the interior of a nondegenerate simple polygon, with the usual Lipschitz boundary; slit or self-touching polygonal sets are not silently included.

2. **Lemma T must explicitly assume dimension two.** “Same as Lemma R” imports arbitrary dimension, whereas the rank-one Hessian analysis uses two variables and a one-variable analytic function. In higher dimensions, a negative-semidefinite Hessian with negative trace need not have rank one or be definite. The one-dimensional manifold conclusion is not licensed in that scope. This does not damage the planar Theorem H after correction.

3. **Supply the missing L-to-C¹ convergence step in H(c).** Local uniform convergence alone is not a general C¹ convergence theorem. Here the eigenfunction equations repair it, as proved in §4 below. Explicitly state eigenvalue convergence before using interior estimates or the harmonic lift.

4. **Replace “new bridge lemma” and repair its attribution.** Lemma R in the Lipschitz/discrete-spectrum setting is directly implied by Bérard–Helffer Lemma 4.3. The weaker arbitrary-domain hypothesis in R only needs an attained Rayleigh infimum; the cutoff proof extends to it, but this formal weakening of the same variational argument does not justify a significant novelty claim.

5. **Repair the approximation citation.** The scout says “Verchota, JFA 59 (1984), appendix.” Ball–Zarnescu's bibliography and discussion identify the **appendix of Verchota's 1982 thesis** and **Proposition 1.12 of the 1984 JFA paper**. I did not independently retrieve and inspect Verchota's original statement, so do not present that locator as directly verified here. Use the fully checked Ball–Zarnescu Theorem 5.1 and Remark 5.3, together with the explanation in §5, instead. Antonini Theorem 3.1(i) independently provides explicit uniform Lipschitz-character bounds.

6. **Do not call Gap G an exact equivalence.** Showing `L(Ω)=E(Ω)` is sufficient to obtain the all-eigenfunction conclusion by this proof; the converse is not established. Hot-spots inequalities could hold for an eigenfunction without that eigenfunction belonging to L. Nor does the cited smooth-domain multiplicity bound, by itself, prove the same bound on a Lipschitz limit: eigenvalue clusters can merge. Until a Lipschitz multiplicity reference or proof is supplied, describe the remaining issue as the **general multiple-eigenvalue case**, not solely an accidental double eigenvalue. This caveat does not affect H(e), which allows any multiplicity.

## 2. Upstream source contract

The authoritative input is family 369, manuscript directory

`preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/`.

The actual statement in [`build/sections/01-introduction.tex`, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/build/sections/01-introduction.tex) assumes a nonempty bounded simply connected planar open set with C∞ boundary and asserts nonvanishing interior gradient for **every** nonzero element of its first positive Neumann eigenspace, including multiple eigenvalues. Thus it supplies exactly the property needed on each smooth approximant, without any simplicity assumption on the approximants.

The catalogue locates this manuscript's old cache in `sources/cache/analysis_geometry/hotspots/`, rather than among the other 79 files in `frontier/sources/analysis-upstream/`. I downloaded the introduction, preliminaries and conclusion from pinned raw URLs into this review's cache and verified byte-for-byte agreement with that old cache. In the preliminaries, `lem:nodal` already uses the same locally-Lipschitz component restriction mechanism as R, at the zero level. `prop:multiplicity` concerns the smooth domain fixed by the manuscript. Its proof is not a source contract for a nonsmooth multiplicity bound.

I checked the catalogue and searched the manuscript's sections for Lipschitz-domain, polygonal, and approximation corollaries. Mentions of Lipschitz *boundary data/multipliers* are not assertions about Lipschitz *domains*. I found no already-stated corollary matching H(d)/(e). The introduction expressly distinguishes smooth domains from corner-domain results. This is a source-scope check only.

## 3. Lemma R and H¹ component cutoffs

Let Ω be any bounded connected open set, let the mean-zero Rayleigh infimum μ be attained by nonzero u, and let C be a component of `{u<t}`, with t>0. Then μ>0: if an attained infimum were zero, the minimizer would have zero weak gradient, hence would be constant on connected Ω, and its zero mean would make it zero. The weak eigenfunction equation holds for every H¹ test function. Interior elliptic regularity makes u analytic, irrespective of the boundary.

Set `f_C=(u−t)1_C`. The cutoff is in H¹(Ω), even if neither Ω nor C has regular boundary. Indeed:

- On a ball compactly contained in Ω, u is Lipschitz. If a∈C and b∉C are in that ball, the segment meets the relative boundary of C, where u=t. The segment argument bounds `|f_C(a)−f_C(b)|` by the same Lipschitz constant times `|a−b|`. Pairs on the same side are immediate.
- Consequently f_C is locally Lipschitz and its weak gradient equals `1_C∇u` almost everywhere. The nontrivial analytic level set `{u=t}` is null; alternatively the Sobolev zero-set derivative property supplies the gradient identity.
- The function and that gradient are globally square-integrable since Ω is bounded, u∈H¹(Ω), and t is finite. The definition of weak derivative against compactly supported tests now gives global H¹ membership. **No zero trace on ∂Ω, boundary integration by parts, or extension of u across ∂Ω is required.**

Write `N_C=∫_C(u−t)²` and `D_C=∫_C|∇u|²`. Testing with f_C gives

`μ N_C − D_C = μ t ∫_C(t−u) > 0`.

Two different components give disjoint restrictions with strictly negative integrals. A nonzero linear combination with mean zero then has Rayleigh quotient strictly less than μ, a contradiction. Therefore

**`{u<t}` is connected for every t>0; `{u>t}` is connected for every t<0.**

Taking t=M when an interior global maximum M is attained gives R exactly. Its signs and strict inequality are correct. Unbounded u near a rough boundary creates no issue: R only assumes a finite attained global maximum, and the more general positive-threshold cutoff is L² without an L∞ hypothesis.

### Direct literature match

[Bérard–Helffer, *Level sets of certain Neumann eigenfunctions under deformation of Lipschitz domains*, AFST 30 (2021), Lemma 4.3 and Remark 4.4, p. 456](https://www.numdam.org/item/AFST_2021_6_30_3_429_0.pdf) states that the positive components of `ϕ_n+aϕ_1`, a>0, number at most n−1. Choose n=2, take `ϕ_2=−u/‖u‖₂`, and choose a so that the constant `aϕ_1=t/‖u‖₂`. There is at least one positive component since u has zero mean. Hence `{u<t}` is connected. Multiplicity causes no exception: any chosen normalized first-positive eigenfunction can be placed second in an orthonormal eigenbasis.

The reference explicitly identifies the Dirichlet analogue in [Gladwell–Zhu, *The Courant–Herrmann conjecture*, ZAMM 83 (2003), Theorem 1, pp. 279–280](https://www.civil.uwaterloo.ca/ggladwell/GW-Zhu2.pdf) and explains the applicability of its argument to Neumann conditions. I read that theorem and its restriction/Rayleigh proof. Cite Bérard–Helffer as the direct Neumann statement, rather than silently attributing a Neumann statement to the Dirichlet paper.

## 4. Lemma T, properness, and Theorem H(a)–(c)

### Maximum-set structure and separation

With **Ω⊂R²** explicitly stipulated, T is correct. At a global maximum, `D²u≤0` and `tr D²u=−μM<0`. If the Hessian is definite the point is isolated. Otherwise it has rank one. Solve `u_s=0` by the analytic implicit-function theorem as `s=φ(σ)`. Locally S lies in that graph. The one-variable analytic function `g(σ)=u(σ,φ(σ))` either equals M identically or has an isolated zero of g−M. In the former case the graph is exactly S locally; in the latter the maximum is isolated and strict. This also covers an isolated *degenerate* maximum, which must not be discarded merely because its Hessian has rank one.

Here is the properness detail that should be made explicit:

1. S is relatively closed. Its set S₁ of non-isolated points is relatively closed as well: a limit of distinct non-isolated points cannot be an isolated point of S.
2. The graph conclusion shows S₁ is locally a single analytic arc, not a branching graph or an immersed curve. It has no manifold boundary in Ω.
3. A connected component C of S₁ is closed in S₁ and hence closed in Ω. With its subspace topology it is a connected, Hausdorff, second-countable one-manifold without boundary. It is therefore a circle or a line.
4. Its embedding in Ω is proper: for any compact K⊂Ω, C∩K is compact, also in the topology of C. Thus an end of a line component cannot accumulate anywhere in the interior of Ω.
5. A bounded simply connected planar domain is homeomorphic to the open disk and hence to R² by the Riemann mapping theorem. Transport C by such a homeomorphism. A circle separates. For a line, properness makes its parametrization extend continuously and injectively to a map `R∪{∞}→R²∪{∞}`; the image is a topological circle in S². Jordan separation again applies.
6. Each open complementary component contains a point outside S, since S has empty interior. No connected subset of Ω\S can join opposite sides of C. This contradicts R.

This proves an auxiliary fact even without approximation: **for a first-positive eigenfunction on a simply connected planar domain with attained Rayleigh infimum, every attained interior global extremum is isolated and strict.** There is no need to assume that an arc has two distinct endpoints on ∂Ω, that its Euclidean closure is a boundary-to-boundary Jordan arc, or that ∂Ω is locally connected. Those stronger endpoint claims would be unjustified; the one-point compactification argument avoids them.

For an exact separation reference, [Hatcher, *Algebraic Topology*, Proposition 2B.1(b), p. 169](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf) gives the complement calculation for an embedded sphere and states its Jordan-curve consequence immediately below. Only topological embedding is required. The one-manifold classification is the usual classification of connected second-countable one-manifolds; the properness argument above is supplied directly.

### H(a) and H(b)

H(a) is correct as written. A strict interior extremum supplies a closed ball with a positive gap between its central value and all boundary values. Uniform convergence on that ball forces an interior extremum of each sufficiently close approximant, contradicting the accepted upstream theorem.

For H(b), use the auxiliary fact just proved: an attained interior global extremum would be strict and is therefore excluded by (a). The original more extended argument using T and R has the same force. It does not need continuity on ∂Ω and therefore remains valid for the stated possibly non-Lipschitz domain, provided nonzero u belongs to L.

### The original definition of L is sufficient for H(c)

Let `μ_k=μ(Ω_k)`, and suppose `u_k→u≠0` locally uniformly as in L. Choose `ψ∈C_c∞(Ω)` with `∫uψ≠0`. Such a ψ exists, and its support is eventually inside Ω_k. Distributional testing gives

`μ_k = (∫u_k(−Δψ))/(∫u_kψ) → (∫u(−Δψ))/(∫uψ) = μ(Ω)`.

The denominator is nonzero eventually. Thus the definition does force eigenvalue convergence for a nonzero limit, despite not explicitly saying so. It would be a mistake to use only geometric inclusion to assert Neumann eigenvalue convergence.

Interior elliptic estimates now upgrade the convergence to C∞ on compact subsets. One direct justification is to set

`h_k(x,s)=exp(√μ_k s)u_k(x)`.

These are harmonic in one additional variable on any fixed interior cylinder for all large k, and converge uniformly there to the analogous lift of u. Interior harmonic derivative estimates give convergence of every derivative on smaller cylinders. In particular `∇u_k→∇u` uniformly on compact subsets of Ω.

If x is an isolated zero of ∇u, choose a small disk B with no other zeros on its closure. On ∂B the gradients ∇u and ∇u_k are connected by a nonvanishing straight-line homotopy for large k. Their winding numbers agree. The normalized gradient of u_k extends over B, so its boundary winding is zero. Hence the index of ∇u at x is zero. An invertible Hessian gives an isolated zero of index `sign det D²u∈{−1,+1}`, and is impossible. This proves **both** assertions in H(c). “Index” must mean the planar vector-field/local Brouwer index of ∇u; a Morse index is not what is asserted.

## 5. Actual smooth approximation and spectral convergence

### A checked topology-preserving approximation source

[Ball–Zarnescu, *Partial regularity and smooth topology-preserving approximations of rough domains*, Calc. Var. PDE 56 (2017), article 13; arXiv:1312.5156v3, **Theorem 5.1**, **Remark 5.3**](https://arxiv.org/pdf/1312.5156v3) is adequate. The theorem constructs inner approximations `Ω_ε={ρ>ε}` for positive ε, using a regularized signed distance. They are bounded C∞ domains, exhaust Ω as ε decreases to zero, and are images of Ω under homeomorphisms of the ambient space. Simple connectivity is therefore preserved. Their closures lie inside Ω. For Lipschitz Ω, Remark 5.3 gives bi-Lipschitz constants bounded independently of sufficiently small ε.

There is also direct control of the *graph* character, not just an unspecified bi-Lipschitz claim. In the proof of Remark 5.3, near each boundary point a fixed good direction n and a fixed neighborhood satisfy positive lower bounds for `∇ρ·n` and an upper bound for `|∇ρ|`, on the interior side. In fixed smaller coordinate cylinders, the positive level sets of ρ are graphs: monotonicity in n gives uniqueness and the endpoint inequalities give existence. Their slopes are bounded by the ratio of those bounds. A finite boundary cover gives fixed chart radii, finite chart number and uniform slope bounds. Thus the same inner family has the uniform Lipschitz character needed for extension operators.

As a separate quantitative confirmation, [Antonini, *Smooth approximation of Lipschitz domains, weak curvatures and isocapacitary estimates*, **Theorem 3.1(i)**, equations **(3.1)–(3.5)**, arXiv:2311.00100v1](https://arxiv.org/pdf/2311.00100v1) constructs smooth inner and outer approximants with measure convergence and explicit upper slope/lower chart-radius bounds. This part assumes only Lipschitz boundary; the W²,q condition belongs to part (ii). Do not mistakenly add that condition to part (i), or combine topology from one arbitrary approximation sequence with extension constants from another. Ball–Zarnescu and its local gradient bounds provide a single sequence with both properties here.

The scout's particular exhaustion proof invokes `x*∈Ω_k` without explaining its origin. Boundary closeness alone needs an interior-side argument. The nested superlevel construction just described supplies eventual containment of every compact set directly and removes this omission.

### The spectral argument is standard and valid

[Ni–Wang, *On the first positive Neumann eigenvalue*, DCDS 17 (2007), **Definition 5.2, Remark 5.3, Proposition 5.4**, pp. 15–18](https://www.aimsciences.org/article/doi/10.3934/dcds.2007.17.1) supplies a precise precedent. Their convergence definition includes uniform chart maps and convergence of characteristic functions. Remark 5.3 describes the fixed-graph-chart sufficient condition. In the proof of Proposition 5.4, Step 5 verifies uniform H¹ extension norms, Step 6 proves the upper bound and Step 7 uses extension compactness plus a small-measure estimate to prove the lower bound. I downloaded and read the full paper, not just its abstract. This is substantially the scout's Lemma A proof.

For clarity, the required norm is controlled by the full Lipschitz character, including chart radii and overlap/number, not merely a bound on graph slopes. The standard extension reference is Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter VI, **Theorem 5**. Its use with uniform constants is also spelled out in Bérard–Helffer **Proposition 2.10**, p. 438, for their controlled family, and in Ni–Wang Step 5 for their convergence class.

For the chosen inner family, restriction of a normalized limit-domain eigenfunction, followed by subtracting its mean, gives `limsup μ_k≤μ`. Normalized u_k then have bounded H¹ norms and uniformly bounded H¹ extensions v_k to a fixed ball. Rellich compactness supplies strong L² and weak H¹ convergence. In dimension two,

`∫_(Ω\Ω_k)|v_k|² ≤ |Ω\Ω_k|^(1/2) ‖v_k‖_L4² →0`.

Thus the restriction of the limit to Ω has norm one and mean zero. Lower semicontinuity on compactly contained exhaustion sets gives its energy at most liminf μ_k. First apply this to a subsequence realizing the liminf to obtain convergence of μ_k; then apply it to any sequence of normalized eigenfunctions. Variational minimality makes every subsequential limit a first-positive eigenfunction. Interior estimates give C∞ local convergence. No H² boundary regularity or uniform convergence on the varying closures is needed.

This proves every assertion of A. In particular L contains a nonzero eigenfunction. If E is one-dimensional, scalar multiplication of one such limit gives all of E. For multiple E, this reasoning does not approximate each prescribed element of E: higher members of a splitting cluster need not be first-positive eigenfunctions of Ω_k. Keeping this limitation is essential.

## 6. Boundary continuity and corrected theorem scope

[Nittka, *Regularity of solutions of linear second order elliptic and parabolic boundary value problems on Lipschitz domains*, JDE 251 (2011), 860–880; arXiv:0906.5285v1, **Proposition 3.6**, pp. 6–7](https://arxiv.org/pdf/0906.5285v1) gives Hölder regularity up to the boundary for the weak Neumann problem with f₀∈L^(p/2), f_j∈L^p, g∈L^(p−1), p>N. Here take N=2, p=4, L=−Δ, β=0, f₀=μu∈L², and f_j=g=0. No bootstrap or smooth boundary is needed. Consequently each planar Lipschitz Neumann eigenfunction has a continuous representative on the compact closure.

Combined with H(b), both closure extrema must occur on the boundary; equality of an interior value to either boundary extremum would itself be an attained global extremum. Thus the displayed strict inequalities in H(d)/(e) are justified.

The corrected deliverable can be stated as follows:

> Assuming family 369's smooth-domain theorem, let Ω be a bounded simply connected planar domain whose mean-zero Neumann Rayleigh infimum is attained. For every nonzero u in the scout's limit set L(Ω), (a) there is no strict interior local extremum; (b) neither global supremum nor global infimum is attained in the interior; and (c) every interior critical point is degenerate and every isolated critical point of ∇u has local index zero. If Ω is Lipschitz, L(Ω) is nontrivial and its elements are continuous on Ω̄. Therefore at least one nonzero first-positive eigenfunction satisfies (a)–(c) and the strict boundary inequalities. If the first positive eigenvalue is simple, every nonzero eigenfunction does.

This covers ordinary simply connected polygons and bounded convex planar domains in the **existential** formulation without a simplicity assumption, and in the **all-eigenfunction** formulation when the eigenvalue is simple. It does not prove nonvanishing gradient on the nonsmooth domain. It does not settle all eigenfunctions at arbitrary multiplicity. It does not establish a nonsmooth non-Lipschitz approximation result. H(a)–(c) still has content on such domains only when membership in L is independently supplied.

## 7. Novelty search and disposition

The decisive positive literature hit is Bérard–Helffer Lemma 4.3: it is stronger than R and uses the same proof idea. Gladwell–Zhu Theorem 1 is its earlier source. The direct spectral-transfer precedent is Ni–Wang Proposition 5.4. Ball–Zarnescu and Antonini show that topology-preserving smoothing and quantitative Lipschitz approximation are established tools rather than new obstacles resolved here.

I also inspected Bañuelos–Pang, *Level sets of Neumann eigenfunctions*, Indiana Univ. Math. J. 55 (2006), **Theorem 1.1**. Its theorem concerns finiteness of level-set components on a smooth, positively curved convex planar domain, not the general nonsmooth extension proposed here. Rohleder's 2024 review describes the then-open general simply connected problem; it cannot, by itself, certify novelty after the assumed September 2026 corpus. Bérard–Helffer §2 expressly revisits Jerison–Nadirashvili's domain-deformation method with attention to uniform geometric constants. I did not obtain the latter's original PDF from AMS (403), so no unverified theorem from that paper is used to close this review.

Search phrases included “Neumann eigenfunction sublevel sets connected”, “Neumann maximum set separate”, “hot spots Lipschitz smooth domains approximation”, “hot spots strict local maximum approximation”, and title searches for all cited approximation and regularity papers. Stored search outputs and primary PDFs/text extractions are in `frontier/sources/hotspots_review_r2/`. The search establishes a concrete prior-art objection to R, not universal absence of prior art for H as a whole.

My recommendation is to retain the corrected statement as a useful conditional corollary or technical note, with the literature attribution above. **Do not advance it as the requested significant novel proof idea.** The substantive theorem doing the hard problem-solving is still the accepted smooth-domain upstream theorem; this proposal transfers it by classical spectral convergence, elementary analytic structure, and planar separation. The extension does add nonsmooth cases to the literal source statement, but that additional scope is not evidence of a new research mechanism. No independently verified argument closes the all-eigenfunction multiple-eigenvalue gap.

## Source-cache record

The review cache contains the pinned upstream introduction/preliminaries/conclusion; primary PDFs and extracted texts for Bérard–Helffer, Gladwell–Zhu, Ball–Zarnescu, Antonini, Ni–Wang, Nittka, Bañuelos–Pang, Rohleder and Hatcher; downloaded search records; and URL/SHA-256 manifests. Failed source retrievals are recorded rather than treated as inspected sources. The only mathematical input accepted without validation is the pinned upstream corpus, as instructed. No numerical tests are relevant to the proof claims reviewed here.
