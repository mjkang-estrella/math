# I218 — Independent proof review of the global Neumann eigenmap

**Verdict: PASS, conditional on the stipulated pinned source results.** The complete theorem in the supplied I214 report is valid with its stated smooth-domain and double-eigenspace hypotheses. No restriction to analytic boundaries, symmetric domains, orthonormal bases, or generic eigenfunctions is needed. No correction to the theorem is required. The explicit estimates and topological details below justify the compressed steps in the report.

This is a mathematical proof verdict only. It makes no contribution, count, priority, significance, or project-integration decision. The other independent review was not read. An early partial checkpoint was written to this file before source verification and the final verdict.

## Exact scope

Let Ω be a nonempty bounded simply connected planar domain with C∞ boundary, μ its first positive Neumann eigenvalue, and V its real eigenspace. Assume dim_R V=2. For every real basis (u,v), F=(u,v) has all the following properties:

- F:Ω→U is a real analytic diffeomorphism, where U is bounded, contains 0, and has the form {r e^(iθ): 0≤r<R(θ)} for a positive C∞ function R on S¹.
- F extends to a homeomorphism of closures. Its boundary restriction is a C∞ diffeomorphism of one-dimensional manifolds.
- For counterclockwise arclength s on ∂Ω, d arg F/ds=det(F,F_s)/|F|² is nowhere zero. Its sign is sign det DF in Ω, and its integral is that sign times 2π. The outward normal of ∂U satisfies y·n(y)>0 everywhere.
- There is a unique c∈Ω at which every member of V vanishes. For each nonzero w∈V, its zero set in the closure is a single smooth embedded arc through c, with two distinct boundary endpoints and orthogonal boundary intersections. Nonproportional members' arcs meet only at c.
- At every boundary point, rank DF=1 and ∂νF=0. The inverse on the closure is not locally Lipschitz at any boundary image. No two-dimensional diffeomorphism of manifolds with boundary is asserted.

The interior-only portion remains a valid narrower conclusion even if one chooses not to use the boundary continuation argument: analytic univalence, bounded star-shaped image containing 0, and the common interior nodal center follow without it. Here the boundary argument also passes, so no retreat to that narrower statement is necessary. No claim is established for unequal first two positive eigenvalues, higher modes, multiply connected domains, or nonsmooth boundaries.

## Actual source dependencies and multiplicity

Revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` of `https://github.com/openai/math`. Family path: `preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/`.

I read the retained actual TeX in place. The precise inputs are `build/sections/01-introduction.tex`, `thm:main` and its final regularity paragraph; and `build/sections/02-preliminaries.tex`, `lem:nodal` and `lem:conformal`. All these source assertions are stipulated true, not audited. Sections 03–06 and the main file/README were also read to bound the comparison with the manuscript. The local retained source hashes match the recorded pinned source identities; details are in the input-authentication file.

`lem:nodal` says explicitly: for 0≠v∈V, both sign sets are connected. This is quantified over the entire real eigenspace, not a chosen spectral basis or the first vector within a multiple block. Its proof uses the first-positive Rayleigh minimum: each nodal restriction v_D is in H¹ and has energy μ||v_D||². If there were three sign components, a nonzero mean-zero combination supported on two would attain that minimum and so would be an eigenfunction, while vanishing on the omitted open component. Analyticity contradicts this. The mean-zero equality case holds against every H¹ test after subtracting its mean. Thus the use for arbitrary a·F is legitimate under multiplicity. No ordered-index extension of Courant is being silently used. The existing `prop:multiplicity` is not an additional conclusion here.

## Interior route: independent checks

### Immersion and proper nodal topology

Evaluation w↦∇w(x) is injective by `thm:main`; with dim V=2 it is an isomorphism. Consequently J=det DF is nonzero throughout the connected Ω and has a constant sign. Interior analyticity gives local analytic inverses.

For nonzero w∈V, mean zero gives both signs and a nonempty zero set Z. The regular-level theorem makes Z a closed embedded one-manifold without boundary in Ω. Every connected component C is closed in Z and hence in Ω. A compact K⊂Ω meets C in a compact set, with the same subspace topology as on C. This verifies properness of the inclusion, not just closedness of an arbitrary parametrization. A connected component is therefore an embedded circle or a properly embedded copy of R.

An embedded circle would bound a disk contained in Ω by simple connectivity. On its compact closed disk, w is zero at the boundary and not identically zero inside by analyticity. A nonzero maximum of |w| is an interior extremum of w or −w, contradicting the gradient input.

For a noncompact component, map Ω homeomorphically onto R², using the stipulated conformal disk parametrization followed by a disk-to-plane homeomorphism. Properness extends the embedded R to an embedded circle after one-point compactification in S². Jordan separation gives exactly two complementary components. Near C the two signs occupy opposite sides. Since each entire sign set is connected and disjoint from C, it stays on its respective side. If another zero component existed, a small regular-level neighborhood of any of its points would contain both signs on just one of those sides, a contradiction. This excludes accumulating families of components as well as any finite extra components. Hence Z itself is one proper line. No assertion about its Euclidean boundary limits has been needed yet.

### Global injectivity, origin and star-shapedness

Given F(p)=F(q)=y, choose a≠0 with a·y=0 and b independent of a. On the one proper line Z(a·F), orient the tangent by T=J₀∇(a·F)/|∇(a·F)|. Then

    d(b·F)(T) = det(∇(a·F),∇(b·F))/|∇(a·F)|.

The numerator is det([a;b])J, a fixed nonzero sign. On an oriented parametrization of this line, b·F is strictly monotone: on the compact parameter interval between any two distinct points, integrate its derivative of strict fixed sign. No completeness of the unit-speed flow is required. Thus p=q. The local analytic inverses patch to an analytic inverse on U=F(Ω).

For every line L through 0, U∩L is the nonempty connected relatively open interval F(Z(a·F)), where ker a=L. If 0 were omitted, the radial projection A of U would be a connected open subset of S¹ with no antipodal pair; an antipodal pair would force its connecting interval U∩L to contain 0. Thus A is a proper open arc of angular length at most π. Its midpoint direction e obeys e·y>0 for all y∈U, including the length-π case because the endpoints are absent. This contradicts the zero integral of e·F. Hence 0∈U, and every radial segment from 0 to a point of U stays in U. Compact-closure continuity of F gives boundedness. This origin argument needs the radial interval property; the convex-hull assertion alone would not suffice.

## Boundary route: continuation, jets and ends

### Smooth nonanalytic boundary and reflection

A holomorphic flattening of the disk near a boundary point, composed with `lem:conformal`, gives a conformal half-disk chart φ that is C∞ up to its diameter with nonzero derivative there. W=w∘φ satisfies

    ΔW+qW=0,    q=μ|φ′|²,    W_y(x,0)=0.

The even reflection H(x,y)=W(x,|y|) is C². In particular H_y agrees at the seam because W_y=0; the potentially sign-changing mixed derivative agrees because W_xy=0 on the diameter, obtained by tangential differentiation of W_y=0. H_xx and H_yy agree directly. The even potential Q is bounded (indeed continuous), though no higher reflected regularity is needed. H solves ΔH+QH=0 distributionally, without a measure on the seam. We do not infer analyticity across the physical boundary.

### Exact Carleman bound and cutoff order

Use the norm for dt dθ, t=log r, on the full reflected punctured disk. For an annularly supported f∈W²,², let g=e^(−τt)f. Since r²Δ=∂t²+∂θ², conjugation gives the multiplier (τ+iξ)²−n² in angular mode n∈Z. Its squared modulus is

    (τ²−n²)² + 2(τ²+n²)ξ² + ξ⁴.

For τ∈{1/2,3/2,5/2,…}, |τ−|n||≥1/2 and τ+|n|≥τ, so the modulus is at least τ/2. Plancherel and density give exactly

    ||r^(−τ)f|| ≤ (2/τ)||r^(−τ)r²Δf||.             (1)

Suppose all one-sided jets of W vanish at the boundary point. Taylor estimates imply |H|+|∇H|≤C_N r^N for every integer N, after choosing sufficiently many one-sided derivatives. These estimates survive even reflection.

Choose 0<R<1 within the chart, χ supported in r<R and equal to 1 for r≤R/2, and η_ε zero for r≤ε and one for r≥2ε. Apply (1) to χη_εH. For each fixed τ choose N>τ. On ε≤r≤2ε, the terms r²(Δη_ε)H and 2r²∇η_ε·∇H have weighted norm O(ε^(N−τ)); the dt dθ measure of that annulus is bounded independently of ε. The removed function and equation terms also converge in the weighted norm. Thus first let ε↓0 with τ fixed. This is not a simultaneous cutoff/large-weight limit.

Writing M=||Q||∞ and A_τ=||r^(−τ)χH||, the resulting inequality is

    A_τ ≤ (2/τ)(MR² A_τ + B_τ),
    B_τ = ||r^(−τ)r²(2∇χ·∇H+(Δχ)H)||
         ≤ C_R(R/2)^(−τ).

Here C_R is independent of τ because the differential operator has acted on χH before multiplication by the weight. For half-integers τ≥4MR², absorption gives

    A_τ ≤ (4/τ) C_R(R/2)^(−τ).

Since r<R/4 and R<1,

    ||H||_(r<R/4, dt dθ) ≤ (R/4)^τ A_τ
                         ≤ (4C_R/τ)2^(−τ) → 0.

The harmless factor 4 is absorbed into the report's unspecified C_R. Flatness ensures the unweighted logarithmic norm here is finite. Thus H vanishes locally, and interior analyticity forces w=0, a contradiction. This proves finite boundary order with no imported strong-unique-continuation theorem.

### Jets give all branches, and all branches are ends

Let k≥1 be the first nonzero one-sided Taylor order. For k≥2 the lowest-degree PDE term gives ΔP_k=0; for k=1 this is automatic. Neumann data gives ∂yP_k(x,0)=0. A real homogeneous harmonic polynomial of positive degree with this condition is A Re(x+iy)^k, A≠0. Therefore W(x,0)=Ax^k+O(|x|^(k+1)); every boundary zero is isolated. The closed boundary-zero set on the compact boundary is consequently finite.

The uniform angular C¹ expansion r^(−k)W(r,θ)=A cos(kθ)+O(r), 0≤θ≤π, proves there are exactly k local branches. Away from small neighborhoods of the k simple cosine roots there are no zeros. In each root neighborhood the angular derivative has a nonzero fixed sign and the endpoint values have opposite signs, so there is exactly one root for each sufficiently small r. There is no room for additional oscillating or hidden branches. Each branch is parametrized over 0<r<δ and converges to the boundary point.

To make the ends argument precise, choose disjoint sufficiently small half-disk neighborhoods of the finitely many boundary zeros, in which this complete branch description holds. Outside them, a boundary collar has no zeros by compactness and nonvanishing trace. Thus Z outside these neighborhoods is contained in a compact subset of Ω. Properness makes each parameter tail of Z eventually avoid that compact set; a connected tail must then stay in one neighborhood and in one of its disjoint branches. Conversely each local branch approaching a boundary point escapes all compact subsets and corresponds to a parameter end. Two distinct such branches cannot be the same end: a sufficiently late connected tail could not occupy both disjoint local branches. Hence the sum of their orders is exactly two, the number of ends of R.

The only alternatives are two simple zeros at distinct boundary points or a single order-two zero. In the latter case both ends tend to the same p, so the one-point compactification gives a Jordan curve C∪{p}⊂closure Ω. Its bounded interior is in Ω. Indeed R²\closure Ω is connected and unbounded, so lies on the unbounded side; any other point of ∂Ω has an exterior neighborhood and cannot lie on the bounded side either. The bounded disk has w=0 at its boundary and w not identically zero inside, again forcing an interior extremum. Thus order two is impossible. There are exactly two distinct simple boundary zeros. Their nonzero tangential derivatives and the k=1 normal ray give smooth, orthogonal endpoints. These conclusions apply to every nonzero w∈V.

## Boundary map, degree and finiteness

If F(p)=0 at a boundary point, choose a nonzero coefficient vector a perpendicular to F_s(p). Then a·F is a nonzero eigenfunction with both zero value and zero tangential derivative there, contradicting the preceding simple-zero result. Thus F has no boundary zero. Taking instead a=(−v(p),u(p)), held constant while differentiating at p, gives

    det(F(p),F_s(p)) = (a·F)_s(p) ≠0.

The map g=F/|F| from ∂Ω to S¹ is consequently a smooth local diffeomorphism. Compactness gives a covering; connectedness makes its degree m a nonzero integer with a fixed sign. Each a·F has exactly two boundary zeros, whereas a covering of absolute degree |m| has 2|m| preimages of the two directions perpendicular to a. Hence |m|=1. Therefore g is a circle diffeomorphism and the boundary image is the smooth embedded radial curve γ(θ)=R(θ)e^(iθ), R>0. Its outward normal satisfies

    γ·n = R² / sqrt(R²+(R′)²) > 0.

Route A already supplies injectivity in Ω. No point of ∂Ω can map into U: take interior points approaching that boundary point and apply the continuous inverse on U to their convergent images. Conversely every point of ∂U comes from ∂Ω by compactness and openness of the interior map. This proves closure bijectivity and thus the closure homeomorphism, as well as the one-dimensional smooth boundary inverse.

For the separate degree route, let U_γ be the bounded inside of γ. If y∉γ, the preimage set in closure Ω is compact and avoids ∂Ω. All preimages are isolated because J≠0, so there are finitely many: otherwise a compact accumulation point would contradict a local inverse. Brouwer degree is therefore sign(J) times their number. The boundary winding number is m inside U_γ and zero outside closure U_γ. Consequently there is exactly one preimage inside and none outside, and m=sign(J). An interior preimage of γ is impossible by local openness, which would produce images outside closure U_γ. This proves F(Ω)=U_γ independently of route A's global injectivity/origin arguments, though both routes deliberately share the nodal and boundary lemmas.

## Common center and inverse limitation

The unique interior preimage c of 0 is basis independent because any other real basis replaces F by AF with A∈GL₂(R). A member a·F vanishes precisely over U∩ker a. Nonproportional coefficient vectors give distinct lines through 0, whose sole intersection is 0. Thus their full closed nodal arcs meet exactly at c, with no common boundary endpoints because F is nonzero on ∂Ω.

Finally ∂νF=0 and F_s≠0 give rank one at every boundary point. For small t>0 the inward normal point p_t=p−tν(p) lies in Ω and

    |F(p_t)−F(p)| ≤ C t²,     |p_t−p|=t.

A local Lipschitz constant L for the closure inverse would imply t≤LCt² for arbitrarily small positive t, a contradiction. Even restricting a Lipschitz bound to nearby interior image points and passing to the boundary limit would give the same contradiction. Thus the report correctly excludes this stronger inverse regularity.

## Reading and review limits

The authentication record gives exact paths, SHA-256 digests, pinned Git blob identities where applicable, and line limits. I read the supplied I214 brief/report/analytic notes/literature file in full and also their retained files; the original reading-and-failures record and input manifest were read in full. I read pinned sections 01–06, main.tex and README completely. The bibliography and boundary-sign figure source were listed but not read; the compiled manuscript PDF was not opened. Only this family's catalogue entry/path metadata was substantively inspected; small adjacent metadata/context was incidentally displayed.

All three retained primary extracted texts were read completely: Jones–Maggioni–Schul, 561 lines/six printed pages; Burdzy 2002, 371 lines/ten PDF pages; Burdzy 2026, 363 lines/seven PDF pages. Their PDFs were hashed in place but not independently rendered or visually read. The PNAS extraction has font substitutions, so it supports the stated qualitative theorem comparison, not a new fine calculation. A truncated early batched display was followed by bounded complete reads of the affected material. No new primary copies were needed. The literature note records the bounded comparison and unreviewed literature.

No subordinate agents, research code, experiments, mathematical tests, repository scans, snapshots, seals, historical replay, shared/ancestor edits, staging, commits, or publication were used. File enumeration was limited to the named I214 source directories; hashing/record creation was administrative bookkeeping. No independent novelty search or worldwide priority conclusion is claimed. The proof passes on the exact scope above; the parent's other decisions remain separate.
