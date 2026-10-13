# I210 independent proof-review finalization

2026-10-12. **PASS WITH PRECISE CORRECTIONS. Theorems 1 and 3 and the specified functional stability bound pass unchanged.** Only the auxiliary arbitrary-measurable two-lattice inference needs the qualification in §2 below. No further proof gap was found.

This is a new review round. I207 saved a substantive review but its provider failed before a terminal response; it did not complete a successful handoff. I reuse its written analysis with attribution, especially [I207 §§2–5](i207-all-height-tiles-proof.md), while independently checking the decisive algebra, staircase, cutoff/retention argument and completion repair here. This document and its detached hashes complete I210, not I207. Pinned results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted. Contribution, priority and the finding count are not adjudicated; eight accepted findings remain eight.

## 1. Exact theorem scope

**Theorem 1.** For every real 2-by-2 matrix A with tr A=0 and d=det A>0, and every finite L>0, the infimum of |F|/covol(Γ) over all bounded Lebesgue-measurable F and full-rank lattices Γ satisfying F+(I+sA)Γ=R² for every real |s|≤L is 1+L²d. A compact nondegenerate parallelogram attains it. Coverage is pointwise at every height. No bound uniform as d↓0, L↑∞ or nonnormality increases is asserted. L=0 separately has value 1.

**Theorem 3.** For compact K⊂R², V of class C¹ on an open neighborhood of K, and L,h>0, assume tr DV=0 and det DV>−L⁻² only on K. For every ε>0, the set

    {(s,p₁+sV₁(p),h[p₂+sV₂(p)]): p∈K, |s|≤L}

has a finite cover by infinite Euclidean cylinders with compact nondegenerate parallelogram perpendicular bases and total base area, counted with multiplicity, at most

    h∫_K [1+L²(det DV)₊]J_h(V) + ε,
    J_h(g)=(1+g₁²+h²g₂²)^(-1/2).

This includes zero-area K and positive-area boundaries; empty K uses the empty cover. Finite counts and meshes can depend on all fixed data, the negative spectral margin, cutoff and ε. The coefficient is optimal for the stated periodic affine problem, not asserted optimal for arbitrary finite cylinder covers. Neither a convex-hull cover nor a result at the singular threshold is claimed.

**Stability.** For C¹ W on a neighborhood of the same K with tr DW=0 on K, Euclidean sup errors in field and derivative at most γ, M bounding ||DV||, and σ=min(1,min_K(1+L²det DV)), the condition L²(2Mγ+γ²)<σ/2 preserves admissibility. The two upper functionals divided by h differ by at most

    |K|[L²(2Mγ+γ²)+(1+L²M²)max(1,h)γ].

This concerns the integral functional, not an optimal cost or one unchanged finite cover.

## 2. Exact auxiliary correction

The original I203 §6 inference, under the source's almost-everywhere definitions of tiling and packing, says an arbitrary measurable completion “contains E and covers the denser lattice” without an almost-everywhere qualification. That pointwise conclusion is false. The accepted counterexample is recorded completely in I207 §5. Its orbit check is valid: exchanging a=(3/4,3/2) for b=(1/4,3/2) preserves E+M for M=(1/2)Z×4Z, while the completed set misses the Λ=Z² orbit of (3/4,1/2). No counterexample to either nominated theorem follows.

Replace the auxiliary inference by this precise statement:

> Let Λ,M be full-rank lattices with covol(Λ)<covol(M). If bounded measurable E tiles by Λ almost everywhere and packs by M almost everywhere, and P is a bounded half-open fundamental parallelogram of M, put F=E∪[P\(E+M)]. Then F is bounded measurable, tiles by M almost everywhere, has area covol(M), and covers by Λ almost everywhere. Its M translates cover pointwise by the definition of the completion. A pointwise common-cover conclusion is available by choosing the source's finite-polytopal E, performing this finite-polytopal completion, and taking its closure; this preserves area and covers both lattices everywhere.

Indeed the periodization of E by M is 0 or 1 almost everywhere. Adding precisely the missing representatives in P makes that of F equal to 1 almost everywhere, giving its area. Containment E⊂F gives the Λ cover only almost everywhere. For finite-polytopal E, only finitely many translates meet bounded P, so the Boolean difference and union defining F have boundary in finitely many line segments. Thus |cl F|=|F|. The translates of compact cl F by each lattice form a locally finite closed union containing an almost-everywhere cover. A nonempty open complement would have positive area, proving pointwise coverage. This does not justify area-preserving closure for arbitrary measurable E and does not prove continuum-height coverage from two heights.

The finite-polytopal option and a.e. conventions were checked directly in the retained 2025 source, printed pp. 1–4. This correction also governs the unqualified two-height summary in I203's literature record. Author files remain unchanged; the parent must integrate the wording repair.

## 3. Independent decisive affine checks

Set k=L√d, D=1+k² and Q=[−1/2,1/2]². With the author's B and G,

    B=[[k,2k],[-1,0]],  G=[[0,2k/D],[-1,2k²/D]],
    det B=2k,  det G=2k/D,
    B⁻¹=[[0,-1],[1/(2k),1/2]],
    (I+tJ)G=[[t,2k(1-kt)/D],[-1,2k(t+k)/D]].

Multiplication gives M_t=B⁻¹(I+tJ)G=[[1,−2k(t+k)/D],[(t−k)/(2k),1]]. Its off-diagonal product is (k²−t²)/D∈[0,k²/D]⊂[0,1). The actual accepted `b:lattice` covers by closed squares for exactly that real-parameter condition, with no individual shear bound. It applies at both endpoints and every irrational height. Therefore BQ+(I+tJ)GZ²=R², and the ratio is D.

I also rechecked the second proof rather than relying on the first: with β=(t+k)/(2k), α=1−β, q=4k²/D and b=1−qβ, the determinant-one right multiplier [[1,−1],[1,0]] turns M_t into the basis u=(b,β), v=(−1,α). Its determinant Δ=1−qαβ=(1+t²)/D is positive. In the stated range α∈[0,1], n_m=ceil(y₀−mα) changes by 0 or −1, so x_m=−m+(b−1)n_m changes by −1 or −b, always at least −1. Since x_m=−Δm+O(1), {m:x_m≤x₀+1} is nonempty and bounded below. Its least member lands in (x₀,x₀+1]; the corresponding vertical coordinate lies in [y₀,y₀+1). Backtracking when b<0 causes no gap. I203's phrase “arbitrary real alpha” is understood within its explicit lemma hypothesis [0,1], not as an extension beyond that range.

For arbitrary A, A²=−dI and S=[e,Ae/√d] is invertible for any e≠0. AS=S√dJ, so F=SBQ, Γ=SGZ² transfer the pointwise cover and multiply area and covolume by the same |det S|. For any other admissible measurable F, integrating its nonnegative periodization over a half-open fundamental cell of (I+LA)Γ gives |F|≥(1+L²d)covol(Γ) by Tonelli. Thus the lower bound covers the full declared class. These checks confirm I207 §§2–3 independently.

## 4. Independent decisive nonlinear checks

Choose M≥1 on a compact neighborhood of K and fix d_*>0 before the mesh. For A=[[a,b],[c,−a]] with ||A||≤M and d≥d_*, −bc=d+a² gives |c|≥d_*/M. The S above with e=e₁ has uniformly bounded norm and inverse, as do B and G for k∈[L√d_*,LM]. Before normalization covol(SGZ²)=2L|c|/(1+L²d), bounded above and away from zero. A common scalar on SB and SG normalizes covolume to one and commutes with I+sA. Both intercept and fundamental-cell radii are consequently uniform at fixed cutoff.

For 0<d<d_*, I201's paid extended-square template has area 1+2L²d and uniformly bounded radius in terms of LM, using an orthogonal zero-diagonal basis. I checked the primary signed identity: δ₁=−sb, δ₂=−sc have negative product; the function is the sum of the square and corner-rectangle indicators and its primal lattice is A_sourceᵀZ²=(I+sA)Z². The rectangles for positive and negative s lie in their endpoint rectangles. Closed locally finite translates promote a.e. tiling to pointwise covering. For d≤0 in the allowed range use the accepted square template; at d=0 omit the added rectangles. Thus the sum of component areas obeys Ψ(A)≤Φ(A)+L²d_*, Φ(A)=1+L²(det A)₊, with uniform radii. Components used as separate bases are nondegenerate.

The uniform inverse bound follows directly from (I+sA)⁻¹=(I−sA)/(1+s²det A): its norm is at most C=(1+LM)/σ at all frozen labels. For each coarse square S choose p_S∈K∩S. The Taylor error is η_δδ with η_δ=√2ω(√2δ)→0; the segment lies in S inside the neighborhood, so spectral assumptions off K are unnecessary.

At fine scale ℓ=δ², apply the infinite affine cover to the actual point p+sV(p). Its chosen center satisfies

    |l−p|≤C(ρℓ+Lη_δδ)=R_δ=o(δ).

Retaining every center within R_δ of S is finite and retains a cover for every p,s before integration. Half-open fundamental cells, rather than overlapping intercept shapes, give

    N_Sℓ²≤(δ+2R_δ+2ρ_Γℓ)²=δ²(1+o(1)).

Retained velocities equal V(p_S)+O(δ); the exact physical cost is hℓ²Ψ(A_S)J_h(W_S(l)). Projection is injective on the intercept plane because direction (1,g₁,hg₂) has first coordinate 1, preserving nondegenerate parallelograms. Summing gives limsup cost at most h∫_KΦ(DV)J_h(V)+hL²d_*|K|. The coarse union lies between K and K_{√2δ}; outer-neighborhood measure convergence handles arbitrary compact boundaries. Choose d_* to control the last error first, then δ for all other errors. No uniformity as d_*↓0 is needed.

Finally |det DW−det DV|≤2Mγ+γ² by column expansion. Positive part is 1-Lipschitz, J_h≤1 and J_h is max(1,h)-Lipschitz. Splitting the functional difference using Φ(DV)≤1+L²M² proves the stated stability estimate. This independently confirms the substantive steps in I207 §4.

## 5. Reading boundary and final disposition

The detailed nonessential Fourier, fractional, parity and regularization checks in I207 §5 are reused with attribution; they are not dependencies of the proofs above and were not converted into new literature claims. Source contracts and exact reading limits are in the [I210 literature record](../sources/i210_all_height_tiles_proof_finalization/literature.md); actual input hashes and the two document hashes are in the [authentication ledger](../experiments/i210_all_height_tiles_proof_finalization/input-authentication.json). No broad search, source-truth audit, research code/tests, subordinate agents, I203/I207 edits, shared-ledger changes, staging, commits or publication occurred. Only the three authorized outputs were written; no source copy was needed.

**Final disposition: PASS WITH PRECISE CORRECTIONS**, confined to the auxiliary wording in §2. Theorems 1 and 3 and functional stability need no mathematical change. I210 review and authentication are complete; integration of the correction belongs to the parent. Contribution and acceptance-count decisions remain open.
