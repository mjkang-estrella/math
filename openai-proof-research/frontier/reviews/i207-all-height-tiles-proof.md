# I207 independent proof review of I203

2026-10-12. **PASS WITH EXPLICIT REPAIRS. Theorems 1 and 3 pass with their stated mathematical scope unchanged.** The repair is confined to the auxiliary two-lattice paragraph in §6: the cited tiling/packing theorem uses almost-everywhere conventions, so an arbitrary measurable completion is initially an almost-everywhere common cover. Its pointwise conclusion needs a boundary/null-set repair. The polytopal closure version stated immediately afterward is valid. A concrete counterexample to the unqualified measurable inference appears below. Neither nominated theorem uses that inference.

This is the independent **proof** gate only. It neither accepts a ninth finding nor decides contribution, novelty, worldwide priority, or significance. The pinned corpus is stipulated true; the checks below concern source contracts and new deductions. No subordinate agents, research code, numerical scans, automated tests, snapshots, seals, historical replay, author-file edits, staging, commits, or publication were used. Partial notes were written before completing the review.

## 1. Exact final scope

**Periodic theorem — PASS.** For every real 2-by-2 matrix A with tr A=0 and d=det A>0, and every finite L>0, the infimum of |F|/covol(Γ), over bounded Lebesgue-measurable F and full-rank lattices Γ satisfying

    F+(I+sA)Γ = R² for every s∈[-L,L],

is 1+L²d. It is attained by a compact nondegenerate parallelogram, with the explicit construction in §2 below. Coverage is pointwise, at every real height, with no exceptional labels or heights. No boundedness uniform in d↓0, L↑∞, or the nonnormality of A is asserted. L=0 has the separate elementary value 1.

**Finite nonlinear theorem — PASS.** Let K⊂R² be compact, let V be C¹ on an open neighborhood of K, and let L,h>0. Assume only on K that tr DV=0 and det DV>−L⁻². For every ε>0, the set

    {(s,p₁+sV₁(p),h[p₂+sV₂(p)]): p∈K, |s|≤L}

has a finite cover by infinite Euclidean cylinders with compact nondegenerate parallelogram bases in their perpendicular planes, whose total base area, counted with multiplicity, is at most

    h ∫_K [1+L²(det DV(p))₊] / sqrt(1+V₁(p)²+h²V₂(p)²) dp + ε.

The empty K case uses the empty cover. Arbitrary compact sets of zero area or positive-area boundary are allowed. No spectral assumption on the surrounding neighborhood is required. The finite count and chosen meshes may depend on the particular data, determinant cutoff, negative spectral margin, ε, and outer-neighborhood convergence of K.

**Stability — PASS in the stated functional sense.** For another C¹ field W on a neighborhood of the same K, with tr DW=0 on K, the specified small C¹ perturbation condition preserves admissibility and gives the displayed Lipschitz estimate for the integral upper functional. It does not compare optimal cylinder costs, move K, or preserve one fixed finite list of cylinders. The derivative norms below are Euclidean operator norms; field norms are Euclidean sup norms on K (neighborhood control is also sufficient).

The coefficient is sharp for the specified periodic affine optimization. There is no claim here that it is sharp among all finite cylinder covers, that a sweep equals its convex hull, or that the theorem extends through the negative singular threshold det DV=−L⁻². The contribution gate remains open.

## 2. Independent affine algebra and source application

Set J=[[0,−1],[1,0]], k=L√d>0, D=1+k², and Q=[−1/2,1/2]². For

    B=[[k,2k],[−1,0]],     G=[[0,2k/D],[−1,2k²/D]],

expansion gives det B=2k and det G=2k/D. Also

    B⁻¹=[[0,−1],[1/(2k),1/2]],
    (I+tJ)G=[[t,2k(1−kt)/D],[−1,2k(t+k)/D]].

Their product is exactly

    M_t=B⁻¹(I+tJ)G=[[1,−2k(t+k)/D],[(t−k)/(2k),1]].

For −k≤t≤k its off-diagonal entries p,r are both nonpositive and satisfy

    pr=(k²−t²)/D ∈ [0,k²/D] ⊂ [0,1).

The actual accepted lemma `b:lattice`, read in full in `linear-coverings.tex`, assumes real parameters with 0≤pr<1 and concludes that the **closed** unit squares centered at [[1,p],[r,1]]Z² cover R². It does not assume |p|<1, |r|<1, p,r≥0, rationality, or strict positivity of their product. Thus it applies directly, without a sign repair or limiting argument. Multiplying its conclusion by B proves BQ+(I+tJ)GZ²=R² for every t in the closed interval. At t=−k and t=k the matrices are respectively [[1,0],[−1,1]] and [[1,−4k²/D],[0,1]], both shear lattices whose closed unit squares cover and tile almost everywhere. Interior heights have det M_t=(1+t²)/D>0. Irrational heights require no separate argument: all calculations and the lemma quantify over real parameters.

This proves attainment in the normalized case, since |BQ|/covol(GZ²)=D. The construction uses different matrices for the intercept shape and the label lattice; it is not a purported similarity between elliptic and hyperbolic derivatives.

For arbitrary A, Cayley–Hamilton gives A²=−dI. With ω=√d and any e≠0, the columns of S=[e,Ae/ω] are independent: dependence would give a real eigenvalue whose square is −d. Direct multiplication gives AS=SωJ. Taking F=SBQ and Γ=SGZ² therefore gives

    F+(I+sA)Γ=S[BQ+(I+ωsJ)GZ²]=R².

An invertible linear image preserves compactness and nondegeneracy of the parallelogram and full lattice rank. Both area and covolume acquire the factor |det S|, so their ratio remains D. Normality and orthogonality of eigenvectors were never used.

For the lower bound, let any admissible bounded measurable F and full-rank Γ be given. Set Λ=(I+LA)Γ and choose a half-open fundamental parallelogram P. The periodization N(x)=Σ_{λ∈Λ}1_F(x−λ) is measurable and ≥1 everywhere by actual coverage. Its integral on P is |F|, by Tonelli and the partition by lattice translates of P. Hence

    |F|≥|P|=det(I+LA)covol(Γ)=(1+L²d)covol(Γ).

This applies to the entire declared measurable class, including disconnected or highly irregular F. Boundedness makes the sum locally finite, but nonnegativity already justifies Tonelli. This lower bound plus the constructed pair establishes the exact infimum without an a priori attainment assumption.

## 3. Staircase proof, including backtracking

I checked this independently of `b:lattice`. In Lemma 2 keep α,β∈[0,1], α+β=1, b≤1, and Δ=αb+β>0. The lattice basis u=(b,β), v=(−1,α) has determinant Δ. Put

    n_m=ceil(y₀−mα),    z_m=mv+n_m(u+v).

Because u+v=(b−1,1), the second coordinate is mα+n_m∈[y₀,y₀+1), including exact integer values. The first coordinate is x_m=−m+(b−1)n_m. For α∈[0,1], including the endpoints, n_{m+1}−n_m∈{0,−1}. Thus x_{m+1}−x_m is −1 or −b, both at least −1. When b<0 the second possibility is an upward jump; no monotonicity of x_m is claimed or needed.

The bounded ceiling error gives x_m=−Δm+O(1). Consequently the set of integers m with x_m≤x₀+1 is nonempty and bounded below. It has a least member m*, even though the sequence can backtrack. Minimality gives x_{m*−1}>x₀+1; the one-step lower bound gives x_{m*}>x₀. Hence z_{m*} lies in (x₀,x₀+1]×[y₀,y₀+1), inside the closed target square. The mixed half-open conventions cover every square boundary needed for Q.

For the application write β=(t+k)/(2k), α=1−β, q=4k²/D, b=1−qβ. Then M_t=[[1,−qβ],[−α,1]]. Adding its second column to its first gives columns u=(1−qβ,β), w=(−qβ,1). Replacing w by w−u gives v=(−1,α). Each operation is unimodular; explicitly [u,v]=M_t[[1,−1],[1,0]], whose right factor has determinant 1. Finally

    Δ=αb+β=1−qαβ=(1+t²)/D>0.

All hypotheses hold, even where b<0. This is a complete second proof of the same pointwise cover. The phrase “arbitrary real alpha” at the end of the author's paragraph should be read within the already stated interval [0,1]; this proof makes no assertion for α outside that interval.

## 4. Uniform templates and the nonlinear passage

Fix M≥1 bounding ||DV|| on a compact neighborhood of K, and fix d_*>0 first. For elliptic A=[[a,b],[c,−a]] with ||A||≤M and d≥d_*, the identity −bc=d+a² gives |c|≥d_*/M. With S=[e₁,Ae₁/√d], both S and S⁻¹ are uniformly bounded: √d≥√d_* and |det S|=|c|/√d≥d_*/M². Also L√d∈[L√d_*,LM], a compact interval separated from zero. This proves boundedness of B,G and their inverses on that interval.

More explicitly, before normalization covol(SGZ²)=2L|c|/(1+L²d). This is bounded above and away from zero. Multiplying **both** SG and SB by the reciprocal square root normalizes covolume to 1 and preserves affine coverage, since scalar dilations commute with I+sA. Intercept and centered fundamental-cell radii then have uniform bounds. There is no unjustified continuous eigenvector choice.

For 0<d<d_*, the I201 fallback has a uniform bound independent of d. In an orthogonal zero-diagonal basis A=[[0,b],[c,0]], bc=−d, use Q∪R_L∪R_{−L}, where R_s is the rectangle from (1/2,1/2) with side vectors (sb,0) and (0,sc). The 1998 signed identity, §2.3 (17)–(21), has parameters δ₁=−sb, δ₂=−sc and lattice A_sourceᵀZ²=(I+sA)Z². Since δ₁δ₂<0, its inverse Fourier expression is the **sum** of the two rectangle indicators. It tiles almost everywhere; the closed locally finite translates cover everywhere. Each R_s lies in R_L or R_{−L} according to the sign of s. The three rectangles have disjoint interiors and total area 1+2L²d. Their radii are bounded in terms of LM; any positive d gives nondegenerate added rectangles. At d=0 omit those rectangles and use the accepted square-zero cover; for −L⁻²<d<0 use `b:affine-cover`. Orthogonal changes preserve all these area and radius statements.

Thus at every frozen derivative one obtains a covolume-one lattice and a finite union of nondegenerate parallelograms of total area Ψ(A), with uniformly bounded support and fundamental-cell radius (for fixed d_*), satisfying

    Ψ(A)≤Φ(A)+L²d_*,    Φ(A)=1+L²(det A)₊.

It is Ψ's continuous **upper bound**, not continuity of the selected lattice or template, that is used in summation.

For nonempty K set σ=min(1,min_K[1+L²det DV])>0. Directly from Cayley–Hamilton,

    (I+sA)⁻¹=(I−sA)/(1+s²det A),    ||(I+sA)⁻¹||≤(1+LM)/σ=:C.

This covers positive, zero, and negative determinants at all frozen labels. The strict negative margin is used precisely here. For small coarse mesh δ, squares S meeting K lie in the chosen neighborhood. Choosing p_S∈K∩S and integrating DV along the segment from p_S to p∈S gives the stated uniform Taylor error η_δδ, with η_δ→0. The segment lies in S, hence in the neighborhood; no trace or determinant condition is needed there.

Use ℓ=δ², centers l∈p_S+ℓΓ_{A_S}, and velocities W_S(l). Infinite affine coverage of the **actual** target p+sV(p) yields f in the chosen intercept template with

    p+sV(p)=l+sW_S(l)+ℓf.

Consequently |(I+sA_S)(l−p)|≤ρℓ+Lη_δδ and |l−p|≤R_δ=C(ρℓ+Lη_δδ)=o(δ). Retaining all lattice centers within R_δ of S is finite, independent of p,s, and retains at least one cover for every target. This establishes coverage before any measure estimate, so no bad boundary set can be discarded.

To count centers, use half-open fundamental cells of area ℓ², not the overlapping intercept templates. They are disjoint and contained in the (R_δ+ρ_Γℓ)-neighborhood of S. Thus

    N_Sℓ²≤(δ+2R_δ+2ρ_Γℓ)²=δ²(1+o(1)).

This distinction is essential and is respected in I203. At retained centers |l−p_S|=O(δ), so W_S(l)=V(p_S)+O(δ). The total physical cost on S is bounded by

    hδ²[Φ(A_S)+L²d_*]J_h(V(p_S))+o(δ²),

uniformly for the fixed cutoff. Splitting the fallback into separate rectangle cylinders preserves total area, with overlaps counted rather than subtracted.

The exact physical factor follows directly by projecting the intercept plane: physical direction is (1,g₁,hg₂), the intercept map multiplies area by h, and projection onto the direction's perpendicular plane multiplies by 1/sqrt(1+g₁²+h²g₂²). Projection is injective on the intercept plane because that direction has first coordinate 1. Bases therefore remain compact nondegenerate parallelograms. Velocities in J_h remain in the original physical coordinates, not in each local lattice basis.

Finally the coarse-square union satisfies K⊂U_δ⊂K_{√2δ}. Compact outer-neighborhood measure converges to |K| even if ∂K has positive area. The function Φ(DV)J_h(V) is continuous on the neighborhood, whether or not the spectral assumptions hold there. Uniform continuity and O(δ⁻²) squares convert the sum to its integral over K, giving limsup cost ≤h∫_KΦJ_h+hL²d_*|K|. Choose d_* first to control the latter error, then δ to control all remaining errors. Sending δ to zero before requiring uniformity as d_*↓0 avoids the degenerating optimal templates. This proves Theorem 3 exactly as scoped.

For stability, columnwise expansion of the determinant gives |det DW−det DV|≤2Mγ+γ². The stated strict inequality leaves 1+L²det DW>σ/2. The positive part is 1-Lipschitz, J_h≤1, and |J_h(W)−J_h(V)|≤Hγ for H=max(1,h). Splitting Φ(DW)J_h(W)−Φ(DV)J_h(V) using the original Φ(DV)≤1+L²M² gives precisely

    |K|[L²(2Mγ+γ²)+(1+L²M²)Hγ]

for the difference of the two functionals divided by h. No closeness or uniform continuity of selected optimal templates is needed.

## 5. Auxiliary claims and the explicit repair

The Fourier surplus bound is correct with the unnormalized Fourier integral convention: for ξ∈Λ_t*\{0}, integrating (N_t−1)e^(−2πiξ·x) over a fundamental cell gives hat(1_F)(ξ), bounded by ∫(N_t−1)=|F|−covol(Λ_t). It forces zeros only at the maximal-covolume heights. Normalized Fourier-series coefficients would carry an additional reciprocal covolume on **both** sides; the displayed bound is unchanged. No continuum of Fourier zeros is justified or used.

The fractional ball argument is valid. Centered fundamental cells of a continuous nonsingular compact matrix path have uniformly bounded radius ρ. Cells meeting B_{R−ρ}(x) have centers in B_R(x); since they cover that ball, their number times the cell area is at least its area. This proves the stated weighted cover and limiting integral D. It gives no indicator rounding. The parity example independently does require at least three residues, since each nonzero difference in (Z/2Z)² belongs to one of the three index-two subgroups. This is compatible with, and irrelevant as an obstruction to, the explicit elliptic construction.

The finite-height thickening estimate is also sound: ||(I+uJ)⁻¹||≤1 and ||J||=1 control residual changes by ηR. For a union of polygons, the newly added area is at most the sum of the individual polygon additions, giving |P|+ηRT+Nπ(ηR)² even when the original polygons overlap. The measurable-cover regularization can be justified by shrinking an open cover of the compact parameter space and taking finitely many residual compact sets inside O; a finite union of closed rectangles inside O then covers those sets. Its cost can be bounded by |O|. These arguments do not create a missing all-height cover.

**Required auxiliary wording repair.** The source *Bounded lattice tiles that pack with another lattice*, §1.2 and Theorem 1.2, defines tiling and packing almost everywhere. Its §1.5 explicitly says “almost fundamental domain.” Accordingly the first measurable-completion assertion in I203 §6 must say “covers almost everywhere” unless pointwise tiling of the input E is separately assumed. The later polytopal closure assertion supplies the valid pointwise version.

Here is a full counterexample to silently replacing that a.e. input by an arbitrary measurable pointwise conclusion. In R² take

    Λ=Z²,  M=(1/2)Z × 4Z,  P=[0,1/2)×[0,4),
    E₀=([0,1/2)×[0,1)) ∪ ([1/2,1)×[1,2)),
    a=(3/4,3/2),  b=(1/4,3/2),  E=(E₀\{a})∪{b}.

E₀ is an exact fundamental domain for Λ and packs by M. E still tiles by Λ almost everywhere and even packs by M pointwise: a and b differ by (1/2,0)∈M, so they merely exchange the representative of one M orbit. Indeed E+M=E₀+M. The prescribed measurable completion is

    F=E ∪ [P\(E+M)]=E ∪ ([0,1/2)×[2,4)).

It is bounded, has area 2=covol(M), contains E, and is an exact M fundamental domain. But F+Λ misses (3/4,1/2): E's sole possible Λ representative was a, which was removed; the added b and the completion all have first-coordinate fractional part below 1/2. Thus completion alone need not yield an actual denser-lattice cover under the source's a.e. convention.

For the source's finite-polytopal choice, completing within P involves only finitely many intersecting M translates, so the completion is piecewise polytopal. Its closure is bounded, has the same area, and its locally finite translates form a closed set containing an a.e. cover, hence an everywhere cover for each of the two lattices. This is the valid repaired two-height consequence. It is nonessential: Theorem 1 has two direct pointwise proofs, and Theorem 3 uses pointwise affine templates with its own retention proof.

## 6. Source contracts, limits, and disposition

The exact source map and actual hashes are recorded in the accompanying literature note and authentication ledger. The decisive accepted contracts are `b:lattice`, `b:zero-diagonal`, `b:affine-cover`, `b:affine-inverse`, `b:projection`, and the finite-retention/outer-neighborhood operation in *Finite cylinder approximation of ruled sets*. Their hypotheses fit the applications above. The external signed identity is used only for the already-paid uniform small-positive-determinant fallback; its sign, transpose, and a.e.-to-closed-cover passage have been checked explicitly.

The three companion introductions were read for scope: they concern existing tetrahedral savings, nilpotent/hyperbolic approximation, and prescribed-tag radial triangular covers. They do not provide a license to extend the current periodic lower bound to arbitrary cylinders or to claim a new tetrahedral bound. No broad novelty search or recursive corpus audit was performed. The author's literature/source-boundary note was read as a statement of claimed dependence, not as independent evidence of priority. The two-lattice source's actual conventions were read to resolve the auxiliary issue above; the unrelated soft-tile and three-subgroup papers were not required as proof dependencies and were not reread.

**Disposition:** preserve Theorems 1 and 3 and the specified functional stability estimate. Qualify the auxiliary arbitrary-measurable two-lattice completion by “almost everywhere,” or explicitly select the finite-polytopal closure construction for the pointwise statement. Apart from that separable repair, I found no missing hypothesis or gap in the nominated results. No contribution decision or finding-count increment follows from this proof verdict.
