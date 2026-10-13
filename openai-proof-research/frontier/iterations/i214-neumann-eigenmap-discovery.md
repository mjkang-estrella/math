# I214 — Global spectral coordinates from a double first Neumann eigenspace

**Disposition: PROVED NOMINATION, conditional on the stipulated pinned theorem.** One bridge is nominated, not separate counts for its interior, boundary, or nodal formulations. Mathematical acceptance and significance/novelty acceptance remain with the parent. No claim of worldwide novelty is made.

## Statement

Let Ω be a nonempty bounded simply connected open subset of R² with C∞ boundary. Let μ>0 be its first positive Neumann eigenvalue and suppose its real eigenspace V has dimension two. For **every** real basis (u,v) of V, put F=(u,v).

Then:

1. F is a real analytic diffeomorphism from Ω onto a bounded domain U containing 0.
2. There is a positive C∞ function R on S¹ such that
   
   U = {r e^(iθ): 0 ≤ r < R(θ)}.
   
   In particular U is strictly star-shaped in the differential sense: its smooth Jordan boundary has outward normal n satisfying y·n(y)>0.
3. F extends to a homeomorphism of closures. Its restriction to ∂Ω is a C∞ diffeomorphism onto ∂U. For any counterclockwise arclength parametrization p(s) of ∂Ω, the lift of arg F(p(s)) has derivative everywhere nonzero and of constant sign; its total change is +2π or −2π according to the sign of det DF in Ω.
4. There is a unique c∈Ω with u(c)=v(c)=0. It is independent of the choice of basis. For every nonzero w∈V, its zero set in the closure is one smooth embedded arc with two distinct boundary endpoints, meeting ∂Ω orthogonally and passing through c. Distinct such arcs intersect only at c unless their eigenfunctions are proportional.

The correct boundary conclusion is **not** that F is a diffeomorphism of two-dimensional manifolds with boundary. At every boundary point DF annihilates the normal and has rank exactly one. Its inverse is not Lipschitz up to that point.

The genuinely new proposed consequence is global univalence of the planar map made from the two lowest nonconstant Neumann modes (in the equal-eigenvalue case), with a smooth star-shaped image and a canonical common nodal point. A local immersion and the already-lower multiplicity bound are not nominated.

## Exact dependencies and reading

Pin: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, repository `https://github.com/openai/math`.

Family: `preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/`.

The source uses μ for the first **positive** eigenvalue; it is the second eigenvalue if the constant mode is counted first. The following exact source labels are used:

- `build/sections/01-introduction.tex`, `thm:main`: ∇w is nowhere zero in Ω for **every** 0≠w∈V, including multiplicity.
- `build/sections/02-preliminaries.tex`, `lem:nodal`: both sign sets of every nonzero w∈V are connected. Its variational proof works for every member of V, not just a selected eigenfunction in an ordered basis.
- Same section, `lem:conformal`: a conformal disk map extends C∞ with nonzero derivative to the boundary. This supplies conformal half-disk charts below.
- The regularity discussion at the end of the introduction: Neumann eigenfunctions are smooth up to ∂Ω and analytic inside.

The proof does not use `prop:multiplicity` as a new conclusion. The dimension-two condition is an explicit hypothesis. It does not use the reciprocal-kernel theorem separately. All six manuscript sections, its main TeX file, README, bibliography, and the included boundary-sign figure source were read in full; no source theorem is audited. Copies and hashes are recorded in `../experiments/i214_neumann_eigenmap/input-authentication.json`.

Only the family-369 catalogue entry and this family's path listing were substantively inspected in the catalogue/tree. No active review outputs or other current lanes were read. Primary literature and exact limits appear in `../sources/i214_neumann_eigenmap/literature.md`.

## Proof, route A: nodal foliation and radial separation

### 1. Immersion

At each x∈Ω, the linear map V→R², w↦∇w(x), has trivial kernel by `thm:main`. With dim V=2 it is an isomorphism. Thus J=det DF never vanishes and has constant sign. The analytic inverse function theorem makes F a local analytic diffeomorphism.

### 2. One proper interior nodal line

Fix 0≠w∈V. Since its mean is zero, w takes both signs. Its zero set Z is a closed regular one-dimensional submanifold of Ω. Each connected component is a circle or an embedded copy of R, and is closed in Ω. The inclusion of a component is proper: intersection with each compact subset of Ω is compact in the component, since it is closed and has its subspace topology.

A circular component bounds a disk contained in Ω, by simple connectivity and Jordan separation. Since w is zero on the circle and is not identically zero on that disk, the maximum of |w| on its closure gives a nonzero interior extremum of w. This contradicts `thm:main`.

A remaining component C is a proper embedded line. It separates Ω into exactly two connected components. For completeness, transport it by a homeomorphism Ω→R² (given by the conformal disk chart followed by a disk-to-plane map). Its one-point compactification is an embedded circle in S². The Jordan theorem gives exactly two complementary components in R² and hence in Ω.

On opposite local sides of C, w has opposite signs. Because each full sign set is connected, the entire positive set lies on one side of C and the entire negative set on the other. Another component C′ would lie in one of these sides and, at any point of C′, have both signs in that same side. This is impossible. Thus **Z itself is one properly embedded line**. This argument does not assume that its ends have limits at individual boundary points; that is established later.

### 3. Global injectivity

Suppose F(p)=F(q)=y. Choose a nonzero vector a perpendicular to y, and choose b linearly independent of a. Then p and q lie on the single line Z(a·F). Put w=a·F and z=b·F.

Orient this line by T=J₀∇w/|∇w|, where J₀ is counterclockwise rotation by π/2. Along it,

   d z(T) = det(∇w,∇z)/|∇w|.

The numerator is a fixed nonzero scalar multiple of det DF, so has a constant nonzero sign. An oriented parametrization of the line therefore makes z strictly monotone. Equality z(p)=z(q) forces p=q. The local analytic inverses now patch to a global analytic inverse on U=F(Ω).

### 4. Lines through zero and a rigorous origin lemma

For every line L through 0, choose nonzero a with L=ker a. Then

   U∩L = F(Z(a·F)).

This is a nonempty connected relatively open interval in L, since the zero line is connected and F is a local diffeomorphism.

Assume 0∉U. Radial projection A={y/|y|:y∈U} is a connected open subset of S¹. It contains no antipodal pair: points of U on opposite rays of the same line would put 0 in the interval U∩L. Hence A is a proper open arc, and its angular length is at most π. Indeed any open arc of length greater than π contains antipodal points. The vector e pointing to its angular midpoint then satisfies e·y>0 for every y∈U, including the length-π case because the arc's endpoints are omitted. Consequently e·F is strictly positive on Ω. This contradicts

   ∫Ω e·F = e·(∫Ωu,∫Ωv)=0.

Thus 0∈U. Each U∩L is now an interval containing 0, so every segment from 0 to a point of U belongs to U. Boundedness follows from continuity of F on the compact closure. This proves interior global coordinates and star-shapedness without any boundary unique-continuation assertion.

## Boundary analysis: no unproved regularity at the edge

The following lemma applies to every nonzero w∈V, without assuming dim V=2.

### 5. Finite order at a smooth nonanalytic boundary

Fix a boundary point where w=0. Use a smooth conformal half-disk chart φ, with real diameter mapping to ∂Ω. W=w∘φ is smooth on the closed half-disk and solves

   ΔW+qW=0,   q=μ|φ′|²,   ∂yW(x,0)=0.

Evenly reflect W and q across y=0. The reflected function is C² (in particular W²,² locally), solves ΔW̃+q̃W̃=0 distributionally, and q̃ is bounded. There is no distribution supported on the diameter because the normal derivative vanishes.

Here is a short proof of the required strong unique continuation, to avoid importing a boundary-analyticity hypothesis. Write t=log r and use the L² norm for dt dθ. For f supported in an annulus and τ a positive half-integer, Fourier transformation in t and Fourier series in θ give

   ||r^(−τ) f|| ≤ (2/τ) ||r^(−τ) r²Δf||.                 (C)

Indeed the conjugated multiplier in angular mode n is (τ+iξ)²−n². Its squared modulus is

   (τ²−n²)² + 2(τ²+n²)ξ² + ξ⁴,

and |τ²−n²|≥τ/2 for integral n and half-integral τ. Plancherel proves (C). Density gives it for annular W²,² functions.

If W̃ vanished to infinite order at 0, its first derivatives would also vanish to every order, from the smooth half-disk Taylor estimates and reflection. Apply (C) to a cutoff of W̃ supported in r<R, equal to W̃ for r<R/2, with an additional cutoff removing r<ε. For fixed τ the inner-cutoff errors tend to zero as ε↓0 by infinite-order vanishing. In the equation term, q̃ is bounded, so r²q̃W̃ is absorbed into the left side for sufficiently large half-integral τ. The remaining commutator is supported where R/2≤r≤R. Its weighted norm is at most C_R(R/2)^(−τ), with C_R independent of τ. Restriction of the left side to r<R/4 then yields

   ||W̃||_(L²(dt dθ), r<R/4) ≤ (C_R/τ) 2^(−τ).

Letting τ→∞ proves W̃=0 there. Interior analyticity then makes w identically zero on Ω, a contradiction.

Thus W has a first nonzero Taylor polynomial P_k, k≥1, at the boundary zero. The PDE implies ΔP_k=0; the Neumann condition implies ∂yP_k(x,0)=0. Therefore

   P_k(x,y)=A Re(x+iy)^k,   A≠0.

In particular the boundary trace has an isolated zero of order k. There are only finitely many boundary zeros, by compactness. This is a smooth-boundary argument, not an analytic-boundary assertion.

The expansion also gives exactly k local nodal branches in the upper half-disk, approaching the rays θ=(2j+1)π/(2k), 0≤j<k. Here are the details needed to exclude hidden branches: uniformly on the closed angular interval, r^(−k)W(r,θ)=A cos(kθ)+O(r), and its angular derivative has the corresponding C¹ expansion. Outside small disjoint neighborhoods of the k simple angular roots the function is nonzero. In each such neighborhood its angular derivative has a fixed nonzero sign and the values at the two ends have opposite signs. Thus there is exactly one root for each small r; the implicit function theorem gives the branch and its limiting angle.

### 6. Exactly two simple boundary zeros

There is only one interior zero line C by step 2. Its two ends must tend to boundary zeros. More explicitly, away from small neighborhoods of the finitely many boundary zeros there are no zeros sufficiently close to ∂Ω, by compactness and continuity. Each end of the proper line eventually leaves every compact subset of Ω. It must therefore eventually stay in one of the disjoint boundary-zero neighborhoods; each local branch there is a tail converging to that boundary point. Hence at most two local branches can occur at any boundary point.

If k=2 at one boundary zero p, both ends of C tend to p. Then C∪{p} is a Jordan curve whose other points lie in Ω. Its bounded complementary disk lies in Ω: the exterior of the smooth Jordan domain Ω is connected, unbounded, and disjoint from the curve, so cannot occupy its bounded side. As in step 2, w=0 on that curve forces a nonzero interior extremum, a contradiction. Orders k≥3 would require at least three ends of C, also impossible.

Thus k=1 at every boundary zero. There are exactly two, they are distinct, and the arc meets the boundary normally (the k=1 local nodal ray is normal). The nonzero gradient gives smooth embeddedness through each endpoint.

### 7. Smooth boundary map and strictly monotone angle

First F(p)≠0 for every p∈∂Ω. Otherwise choose a nonzero a perpendicular to ∂τF(p). The eigenfunction a·F has both value and tangential derivative zero at p, contradicting step 6. This also covers ∂τF(p)=0.

For any p∈∂Ω choose a=(−v(p),u(p)). Then a≠0 and a·F(p)=0, so step 6 yields

   det(F(p),∂τF(p)) = ∂τ(a·F)(p) ≠0.

Therefore the angular map g=F/|F|:∂Ω→S¹ is a smooth local diffeomorphism with derivative of constant sign. It is a covering of some nonzero degree m. For any fixed nonzero a, a·F has exactly two boundary zeros by step 6. But a covering of absolute degree |m| takes each of the two directions perpendicular to a exactly |m| times. Thus 2|m|=2, and |m|=1.

Consequently g is a diffeomorphism of circles. Writing the boundary radius as R(θ)=|F(g^(−1)(e^(iθ)))| gives positive C∞ R. The boundary curve γ(θ)=R(θ)e^(iθ) is a smooth embedding. Its determinant det(γ,γ′)=R² is positive, which is precisely strict star-shapedness.

To identify this with ∂U using route A, no boundary point can map into U: if x_j∈Ω tends to p∈∂Ω and F(p)∈U, continuity of the inverse on U would imply x_j→F^(−1)(F(p))∈Ω, a contradiction. Conversely every point of ∂U is the image of a boundary point, by compactness. Thus F(∂Ω)=∂U. Interior injectivity, boundary injectivity, and disjoint images give a continuous bijection of compact closures, hence a homeomorphism. The boundary inverse is smooth because g is. The orientation assertion follows from the degree of the interior local diffeomorphism.

### 8. Common nodal point and the precise boundary limitation

Since 0∈U and F is injective, c=F^(−1)(0) exists and is unique. A basis change replaces F by AF for A∈GL₂(R), preserving this point. Each nodal arc is the preimage of the interval U∩ker a. Two distinct origin lines meet only at 0, proving the common-intersection assertion.

At the boundary ∂νF=0. The determinant in step 7 proves ∂τF≠0, so rank DF=1. A C¹ inverse of closures would contradict the chain rule. In fact with p_t=p−tν(p), smoothness and the Neumann condition give |F(p_t)−F(p)|=O(t²), whereas |p_t−p|=t. Thus the inverse is not Lipschitz there. This limitation holds even for the disk, not just an exceptional domain.

## Route B: variational boundary topology and degree

This is a second route to the global conclusion, sharing only immersion and the nodal/boundary lemmas, not the radial-projection origin argument or the monotonicity proof of injectivity.

The connected-sign-set input can be derived directly from the first-positive Rayleigh variational principle: the restriction w_D to each sign component has energy μ||w_D||². If there are three sign components, choose a nonzero mean-zero combination of restrictions to two. It attains the first-positive quotient, hence is an eigenfunction, but vanishes on the third open component, contradicting analyticity. This handles multiplicity correctly.

Use steps 2, 5, 6, and 7 to obtain the boundary Jordan curve γ with strictly monotone angle and |deg g|=1. Let U_γ be its bounded star-shaped interior. The degree of F at y∉γ equals the winding number of γ about y, namely m=±1 inside U_γ and 0 outside. Every preimage in Ω is regular, of the same sign s=sign det DF. Such preimages are finite: an infinite sequence would accumulate either at an interior preimage, contrary to local injectivity, or at a boundary point mapping into γ, contrary to y∉γ. Thus

   degree(F,Ω,y) = s · #(F^(−1)(y)).

It follows that every y∈U_γ has exactly one preimage, that m=s, and that no point outside U_γ∪γ is attained. An interior point cannot map onto γ because local openness would then give image points outside U_γ∪γ. Hence F(Ω)=U_γ and F is injective. This independently supplies both global univalence and 0∈F(Ω), and agrees with route A.

## Counterexample and scope checks

- **Disk:** for a disk of radius a the first double eigenspace has basis J₁(αr/a)cosθ, J₁(αr/a)sinθ, where α is the first positive zero of J₁′. The eigenmap is a radial map to a disk; the normal derivative at r=a is zero. This is consistent with all asserted conclusions and directly rules out a smooth/Lipschitz inverse of closures. No numerical Bessel evaluation is used.
- **Unequal first two positive eigenvalues:** no claim. Their linear combinations are generally not first eigenfunctions; the essential all-directions gradient argument fails.
- **One-dimensional V:** the map to R² is unavailable. The boundary-zero lemma still applies, but is supporting material, not another nomination.
- **Higher eigenvalues:** the variational connectedness of both signs fails in general, so neither the proper-line proof nor the boundary degree follows.
- **Holes:** a nodal component need not separate the domain, and a circular zero set need not enclose a disk in Ω. Both proofs explicitly need simple connectivity.
- **Rough boundary:** reflection in a smooth conformal chart, Taylor expansion, and the smooth boundary embedding are not asserted. The interior proof above is stated under the original smooth hypotheses; it is not silently extended to the rough-boundary case.
- **No uniform condition-number, convex-image, conformality, or boundary inverse Hölder exponent is claimed.** The Neumann degeneracy prevents a uniform global lower Lipschitz bound on the closure.

## Literature comparison and significance limit

Three primary works were read completely and retained with hashes: Jones–Maggioni–Schul (PNAS 2008, six pages), Burdzy (arXiv:math/0203017v1, ten pages), and Burdzy (arXiv:2610.12622v1, seven pages). Exact titles, theorem comparisons, retrieval URLs, and reading limits are in the literature file.

The comparison supports a bounded conclusion: the PNAS theorem provides two suitably selected local coordinate functions in dimension two, with frequencies depending on the local radius. It does not give global injectivity of a fixed lowest eigenspace or the present boundary assertion. The 2002 nodal paper gives geometric localization by mirror coupling, not this global eigenmap. The 2026 note propagates hot-spots extrema to rough domains with a simple eigenvalue; it does not concern a double eigenspace or global spectral coordinates. No duplicate of this bridge occurs in the completely read family-369 manuscript.

This is a substantive global spectral-embedding consequence of the stipulated theorem, obtained using elementary but necessary topology and a boundary argument. The parent should assess whether that consequence clears the project's significance threshold. The searches and these three comparisons do not establish worldwide priority. The 2010 full proof paper cited by the PNAS announcement, general harmonic-map univalence literature, and all literature citing the October 2026 source have not been exhaustively reviewed. Neither gate is represented as passed here.
