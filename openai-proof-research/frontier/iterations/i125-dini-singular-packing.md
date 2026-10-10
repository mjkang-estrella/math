# I125 — Original I122 audit and Dini-coefficient singular packing

2026-10-10. The source theorems **and lower operations** at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. This report does not audit their truth. External literature is compared at its actual hypotheses and proof operations, not stipulated by association. No children, shared edits, staging, commits or publication. I123/I124 outputs are not dependencies.

**Disposition:** no substantial nomination; Screen C remains unresolved. The substantive I122 partial claims pass independently at their expressly restricted scopes. One literal illustrative equality fails at general Λ: I122 defined Ω(r)=∫₀ʳω(√Λt)dt/t, so for ω(s)=log(e/s)⁻² it equals **1/log(e/(√Λr))**, not 1/log(e/r), unless Λ=1. The original annular estimate and divergent-full-tail conclusion pass without repair. The preliminary verdict file is preserved, with this correction in a separate audit addendum. Neither formula is a counterexample to Screen C.

I119's complete weighted-chain pass is preserved; I116/I113 passes are inherited, not reaudited. XI is still unpaid and R113 is **PARKED**. Eight accepted findings remain eight. The planar polynomial graph-complexity screen stays unresolved; the constrained Ball–Evans direction remains an I07 overlap.

## 1. Original audit before continuation

The immutable original report has SHA-256 `b9e5117d6871a53feab12fdea884088c023f6d88a604cd1f971eafdcc599dc74`. The recursive I122 task has SHA-256 `7f2accc06c95b5ccc50e7ca2b898962fd083e4d59f8f3b6275345c9604682024`. Its referenced I119 task has SHA-256 `417f8386d54303348d2bfa6747163f8ebf196cf8cefe640a9135eddb5eadf961`. All complete brief fields, including prior objections and parent responses, are frozen. The supplied original I122 report and parent response are also bound to their disk originals. The following verdicts concern originals, not strengthened replacements.

| Original claim | Verdict | Exact scope |
|---|---|---|
| Ellipsoid/amplitude transform | PASS without repairs | All nonnegative fixed-trace H¹ competitors, with domain and modulus margins |
| WE and RD | PASS without repairs | Assumed Lipschitz bound pays both solution and cone energy; a.e. derivatives and positive-radius absolute continuity |
| Annular Dini accounting | PASS without repairs | Bounded-overlap increments; no summation of whole tails |
| Literal logarithmic Ω example for arbitrary Λ | FAIL | Missing √Λ in the logarithm; preliminary overbroad verdict retained separately |
| Covariance CB | PASS without repairs | Explicit ND hypothesis, free-boundary centers, enclosing ellipsoids inside the domain |
| Equal-energy one-dimensional minimizers | PASS without repairs | Obstruction to distance from an arbitrarily selected minimizer only |
| Complete compatible coordinate subclass | PASS without repairs | Energy identity for bi-Lipschitz maps; geometric singular-set identity requires the stated C¹ diffeomorphism |
| Tubular and rectifiable transport constants | PASS without repairs | Interior margin, finite image cover and source normalization recorded |
| Determinant and curvature obstructions | PASS without repairs | Obstructions to exact flattening, not to packing |
| Rotating example: map, coefficients, modulus | PASS without repairs | Global bi-Lipschitz on the ball, including 0; continuous but non-Dini coefficients |
| Rotating example: minimality and all blowups | PASS without repairs | Absolute minimality also across 0; every blowup flat; no unique tangent |
| Full Screen C packing/rectifiability | unresolved | Original report correctly did not claim it |

### 1.1 Transform, competitors, and differentiation

At a free-boundary center x₀, let T=A(x₀)¹ᐟ², q₀=q(x₀), and v(y)=u(x₀+Ty)/q₀. The chain rule gives ∇ₓu=q₀T⁻¹∇ᵧv, while dx=det(T)dy. Thus the common factor is det(T)q₀² and the coefficients are exactly

Ã(y)=T⁻¹A(x₀+Ty)T⁻¹, Q̃(y)=q(x₀+Ty)/q₀.

The linear map bijects H¹₀ differences on corresponding domains. It preserves nonnegativity and absolute local minimality. At zero Ã=I, Q̃=1. On Bᵣ, the coefficient error is at most C(λ,Λ)ω(√Λr), provided √Λr≤1. Lip(v)≤√ΛL/λ. These facts require no derivative of A.

For a.e. r, the cone z(sθ)=(s/r)v(rθ) has the prescribed Sobolev trace and energy bounded by C(n)(1+Lip(v)²)rⁿ. Both coefficient comparisons are therefore justified; an estimate for the solution alone would not have sufficed. Write E=∫Bᵣ(|∇v|²+χᵥ₊), H=∫∂Bᵣv². The cone identity and differentiated W=r⁻ⁿE−r⁻ⁿ⁻¹H give

E(z;Bᵣ)=(r/n)∫∂Bᵣ(|∇τv|²+v²/r²+χᵥ₊),

W′=nr⁻ⁿ⁻¹(E(z;Bᵣ)−E(v;Bᵣ))+r⁻ⁿ∫∂Bᵣ(∂ᵣv−v/r)².

The phase trace agrees for a.e. radius by coarea. H and E have the required absolute continuity on [s,R], s>0. Consequently Φ=W+C₀Ω is nondecreasing and

∫Bᴿ∖Bˢ |v−y·∇v|²/|y|ⁿ⁺² ≤ Φ(R)−Φ(s). (RD)

This independently verifies the displayed exponents, rather than treating problematic extracted exponents in another paper as premises. The source operation is Sobral's freezing and homogeneous comparison, with I122's Lipschitz hypothesis explicitly paying competitor energy. It is technical.

For geometric radii, each t belongs to only boundedly many intervals (a2⁻ʲ,b2⁻ʲ); Tonelli proves the annular sum bound. The corrected logarithmic computation above follows by s=√Λt. Its dyadic tail is still comparable to 1/j, so recharging Ω at each scale still diverges. The incorrect exact equality is not retroactively passed by making this correction.

### 1.2 Covariance, phase nonuniqueness, and transport

For unnormalized covariance M=∫(y−X)⊗(y−X)dμ and its eigenpair (λᵢ,eᵢ), set fᵧ(z)=u(z)−(z−y)·∇u(z). Barycenter cancellation gives ∫[(y−X)·eᵢ]fᵧ(z)dμ=λᵢeᵢ·∇u(z). Cauchy–Schwarz yields λᵢ|eᵢ·∇u|²≤∫|fᵧ|²dμ, including λᵢ=0. Under the **original extra hypothesis**

∫B₄ᵣ(x)∖B₃ᵣ(x) Σᵢ₌₁ᵏ⁺¹|eᵢ·∇u|² ≥ c rⁿ, (ND)

one bounds λₖ₊₁, then the covariance tail by (n−k)λₖ₊₁. For y∈Bᵣ(x), the common integration annulus lies between normalized radii ar and br about y, a=2/√Λ, b=5/√λ. The scalar fᵧ is affine invariant up to the amplitude q(y). Jacobians, amplitudes, and powers of normalized radius are bounded using λ,Λ. This proves exactly

βᵏμ(x,r)² ≤ C(n,λ,Λ,L,c)r⁻ᵏ∫[Φᵧ(br)−Φᵧ(ar)]dμ(y). (CB)

There is no common-center metric assertion hidden here. The domain margin is essential. Original I122 did not pay ND for the geometric singular set.

On (−R,R), trace h=R/2 gives the constant h and (|x|−(R−h))₊ energy 2R each, with squared gradient distance R. For any nonnegative H¹ competitor, either it is everywhere positive, costing at least 2R in phase measure, or it has a zero; the two intervals from that zero to the endpoints each cost at least 2h by a²+1≥2|a| on the positive set. This establishes minimality, not just equality between two competitors. It refutes only the proposed estimate toward an arbitrarily chosen minimizer.

For orientation-preserving C¹ bi-Lipschitz F, J=det DF and A=JDF⁻¹DF⁻ᵀ, q²=J, change of variables proves J_{A,q}(U∘F;O)=J₁(U;F(O)) for every competitor. The inverse gives the converse. The a.e. chain and area formulas also prove energy transport for the nonsmooth bi-Lipschitz twist. C¹ structure, however, is used for exact transport of geometric regularity in both directions.

Let L_F=Lip F, L_I=Lip F⁻¹, K interior with sufficient margin. F sends Nᵣ(S∩K) into N_{L_F r}(S′∩F(K)); inverse volume distortion is ≤L_Iⁿ. Hence the local source packing yields C L_IⁿL_F⁷r⁷ after a finite interior cover. The source Lipschitz/energy normalization, its radius restrictions and image margin enter C. For radii larger than an image-chart radius, the elementary volume bound enlarges C by the inverse seventh power of that radius. Hⁿ⁻⁷ and rectifiability transport with factor L_Iⁿ⁻⁷. This is the entire compatible subclass, conditional only on its stated coefficient and map hypotheses; it is not the arbitrary-matrix theorem.

Exact realization requires DFᵀDF=q²A⁻¹ and det DF=q², so det A=(q²)ⁿ⁻². A=I with nonconstant q fails for n≥3. Determinant compatibility alone fails for the smooth metric diag(e²ˣ¹,e⁻²ˣ¹,1,…,1): t=eˣ¹ gives dt²+t⁻²dx₂², curvature −2/t². On a bounded local domain its coefficients are uniformly elliptic. A Euclidean pullback is flat. These are route obstructions only.

### 1.3 Rotating example, including zero

With J the rotation generator in the (x₁,xₙ)-plane, θ(r)=log log(e/r), b=rθ′=−1/log(e/r), F(x)=Rθ(r)x, one has

DF=Rθ(I+bJe⊗e), (Je⊗e)²=0, det DF=1,

A=I−b(Je⊗e+e⊗Je)+b²Je⊗Je.

Radius preservation gives the continuous inverse R_{−θ(|y|)}y. Both derivative norms are ≤2 off zero. Integration along a segment avoiding zero proves the Lipschitz bound; split a segment through zero and use continuity for the remaining case. Thus the map and inverse are globally 2-Lipschitz on B₁. Singular values give ¼I≤A≤4I, and A→I at zero.

For point separation ρ, if one radius is ≤√ρ, both deviations from I are O(1/log(e/ρ)). Otherwise the joining segment stays outside a fixed multiple of √ρ for small ρ, and |∇A|≤C/[r log(e/r)] yields O(√ρ). Larger ρ are absorbed by a fixed constant. The directional off-diagonal entry for |Je|=1 has size |b|, so any admissible modulus dominates c/log(e/r) at distance r from zero and cannot be Dini. Its square is integrable against dr/r.

For U=(yₙ)₊, |∇w|²+χ_{w>0}≥2∂ₙw a.e. for nonnegative H¹ w, with equality for U. The gradient of w is zero a.e. on {w=0}; integration of the fixed-trace difference's derivative is zero. This proves absolute local minimality, and transport proves it for u=U∘F even on domains containing zero.

On every fixed compact set away from x=0, θ(r|x|)−θ(r)→0 uniformly. The small omitted ball is controlled by the common Lipschitz constant. Every blowup subsequence has a further subsequence with θ(r) converging modulo 2π; its limit is (Rθ* x)ₙ,₊. Conversely every such angle is attained because θ is continuous and unbounded. Any existing blowup limit must therefore be one of these halfspaces. Distinct normals rule out a tangent hypersurface at zero. This construction passes exactly as a **non-Dini** test; products or constant adjustments do not turn it into a Screen C counterexample.

## 2. Exact target and source-operation boundary

Fix n≥8, 0<λ≤1≤Λ, L, and the **entire specified** nondecreasing ω:[0,1]→[0,∞), ω(0)=0, ∫₀¹ω(t)dt/t<∞. On B₄, A=Aᵀ, λI≤A≤ΛI, λ≤q≤Λ and ||A(x)−A(y)||+|q(x)−q(y)|≤ω(|x−y|) for |x−y|≤1. Let u≥0 be L-Lipschitz and minimize

J_{A,q}(u;O)=∫O[∇uᵀA∇u+q²χ_{u>0}]

against every nonnegative v with v−u∈H¹₀(O), O compactly contained in B₄. S consists of free-boundary points not locally a C¹ hypersurface with the positive phase on one side. The target remains

|Nᵣ(S∩B₁)|≤C(n,λ,Λ,L,ω)r⁷, 0<r<1/10. (Screen C)

No power gauge, square-root-Dini condition, integrable metric, alternative singular set, or almost-minimizer class has replaced this statement. The arguments below do not establish it, its Hⁿ⁻⁷ consequence, or rectifiability.

The full [Edelen–Engelstein v3](https://arxiv.org/abs/1702.04325v3) proof was read through its final rectifiability argument: rigidity, quantitative cone splitting and its dichotomy, L² covariance approximation, the centered small-density-drop packing lemma using discrete Reifenberg, good and bad trees, alternation overcoming repeated overlaps, finite density-drop recursion, and the separate rectifiability step. Inserting the stipulated critical dimension seven in that constant/Hölder machinery is technical. Their power-gauge extensions do not state the present matrix-Dini theorem.

The full [Sobral v2](https://arxiv.org/abs/2604.12712v2) was read, including the §5.1 Bernoulli calculation. It already uses Dini freezing and homogeneous competitors. Its Alt–Phillips sections concern a different energy; neither their regularity conclusions nor extracted exponent typos are imported. The [variable-matrix companion v2](https://arxiv.org/abs/1909.05043v2) assumes Hölder coefficients; its complete coordinate-change lemma was read. L is assumed here, not inferred by extending its later Lipschitz theorem.

Two stronger companions were newly retrieved and selectively extracted. The complete [De Silva–Savin v1](https://arxiv.org/abs/1901.02007v1), including its final flatness iteration, was read. The relevant complete proof chains in [David–Engelstein–Toro v2](https://arxiv.org/abs/1702.06580v2), §3 and §§7–9, were read through their endings. The latter's harmonic replacements, NTA/boundary-Harnack comparison and fractional-power radius changes feed a weak-solution flatness argument with error τ small relative to σ². Its quoted antecedent lemmas are identified, not represented as newly proved here. No full audit of every cited classical paper is claimed, and no external theorem at an enlarged scope is used to close a gap.

Searches through 2026-10-10 locate other Dini obstacle, spectral-partition and singular-potential problems, but titles/snippets are not theorem premises here. The report makes no exhaustive literature-absence or worldwide-priority assertion. The pinned Bernoulli statement, history, full reductions and consequences were read as accepted operations, without reopening classification truth. The ledger overlap screen does not reopen the planar or Ball–Evans branches.

## 3. Route one: compactness, covariance summation, and the geometric gap

### 3.1 Uniform clearing with explicit constants

There is ε_cl=ε_cl(n,λ,Λ,L)>0 such that, whenever Bᵣ(x) is interior,

supBᵣ(x) u ≤ ε_cl r ⇒ u=0 on Bᵣ/₂(x). (CL)

This uses only bounded ellipticity, positive phase cost, minimality and the assumed Lipschitz bound. Scale to B₁; let P={u>0}, F(t)=|P∩Bₜ|, Mₜ=supBₜu, C₀=Λ/λ². For s<t, use v=min(u,h), where h=0 in Bₛ and h=Mₜ(|x|−s)/(t−s) in the annulus. Its outer trace equals u after taking the minimum. Cancelling where u≤h, discarding nonnegative Dirichlet energy where u>h, and noting that phase costs cancel in the annulus gives

F(s) ≤ C₀ Mₜ²(t−s)⁻² F(t). (3.1)

Use K=max(1,L), Tⱼ=1/2+2⁻ʲ⁻², tⱼ=(Tⱼ+Tⱼ₊₁)/2 and dⱼ=2⁻ʲ⁻⁴. If F(Tⱼ)<vₙdⱼⁿ, Lipschitz continuity implies

M_{tⱼ} ≤ K[F(Tⱼ)/vₙ]¹ᐟⁿ.

Indeed a positive value a at distance at least dⱼ from ∂B_{Tⱼ} forces a positive ball of radius min(a/K,dⱼ); the alternative radius dⱼ contradicts the strict measure bound. Hence, with D=256C₀K²vₙ⁻²ᐟⁿ,

F(Tⱼ₊₁) ≤ D4ʲ F(Tⱼ)¹⁺²ᐟⁿ.

Choose a>0 with a≤vₙ2⁻⁴ⁿ/2 and Da²ᐟⁿ≤2⁻ⁿ. If F(T₀)≤a, induction gives F(Tⱼ)≤a2⁻ⁿʲ, and therefore u=0 in B₁/₂. Applying (3.1) with s=3/4,t=1 yields F(T₀)≤16C₀vₙ M₁². For example

ε_cl=min{1,[a/(32C₀vₙ)]¹ᐟ²}

suffices. At any free-boundary point, (CL) implies supBᵣu>ε_cl r, since an open zero ball would contradict that point being on the boundary. Combining this with Lip(u) gives a positive ball of radius c(n,λ,Λ,L)r within a comparable ball at every free-boundary point. In particular the free boundary is porous and Lebesgue null. This is a paid elementary cutoff iteration, not a sharp singular-packing theorem.

### 3.2 Phase and energy compactness with selection, not a gap estimate

Consider a sequence on a fixed ball with common local Lipschitz and value bounds, uniform ellipticity, and coefficients converging uniformly on compact sets. Arzelà–Ascoli gives uⱼ→u locally uniformly after selection and ∇uⱼ⇀∇u locally in L². For B_R interior choose η=1 on B_{R−δ}, η=0 near ∂B_R, |∇η|≤C/δ. The competitor wⱼ=ηu+(1−η)uⱼ is nonnegative with the trace of uⱼ. If εⱼ=||uⱼ−u||∞, the shell energy is bounded by

C Rⁿ⁻¹[(1+K²)δ+εⱼ²/δ].

Minimality followed by j→∞ and then δ→0 gives limsup Jⱼ(uⱼ;B_R)≤J(u;B_R). Weak lower semicontinuity of the quadratic energy and Fatou's inequality for phases give the reverse bound. Their two nonnegative lower-semicontinuity deficits must separately vanish. Thus

χ_{uⱼ>0}→χ_{u>0} in L¹_loc, ∇uⱼ→∇u in L²_loc, Jⱼ(uⱼ;B_R)→J(u;B_R).

For the phase conclusion, local uniform convergence already gives eventual positivity at each point where u>0; equality of the weighted phase integrals, q bounded below, removes the remaining mass on {u=0}. Strong gradient convergence follows from ellipticity, weak convergence and convergence of quadratic energies. For any compactly supported H¹ competitor for u, perform the same gluing outside its support, where the function is again u; no Lipschitz bound on the arbitrary competitor is needed. Passing to the limit proves minimality of u.

(CL) rules out positive incursions of uⱼ into the interior of {u=0}. Positivity on compact subsets of {u>0} follows from uniform convergence. Conversely a ball around a limit free-boundary point cannot avoid all approximating free boundaries: if uⱼ is identically zero there it contradicts nearby positivity of u; if uⱼ is positive throughout it, the Euler equation passes to the limit, and the strong maximum principle for nonnegative uniformly elliptic harmonic functions contradicts a zero with nearby positivity. This proves local Hausdorff convergence of free boundaries. The maximum principle is the ordinary interior linear elliptic one, not a free-boundary regularity theorem.

Under rescaling at a free-boundary point, ω(Rr)→0 for every fixed R. The preceding selection gives a nonzero global frozen minimizer. RD, its finite Weiss limit, and strong energy convergence make every such blowup one-homogeneous. No rate or closeness to an arbitrarily selected frozen minimizer is inferred. The original one-dimensional example is fully consistent with this argument.

### 3.3 A uniform ND statement at its actual effective-stratum scope

Normalize on B₈ with f(0)=0 and Lip(f)≤K. Quantitative symmetry is measured in the scale-invariant norm r⁻ⁿ⁻²∫Bᵣ|f−h|². Let “(k+1)-symmetric” mean one-homogeneous and invariant under translations in a (k+1)-plane. For every ε>0 there are δ>0 and c>0, depending on n,K,k,ε, such that a function δ-close to a one-homogeneous function on B₈ and at least ε-distant from every (k+1)-symmetric function on B₁ satisfies

inf_{dim V=k+1} ∫B₄∖B₃ |proj_V∇f|² ≥ c. (3.2)

Proof: otherwise take δⱼ→0, an annular integral tending to zero, and convergent subsequences of the Lipschitz functions and planes. The limit is homogeneous; weak gradient convergence implies its derivatives along the limiting plane vanish on the annulus. Homogeneity propagates that assertion to every positive radius. Vanishing distributional directional derivatives imply translation invariance; the limit contradicts the distance assumption. Compactness also justifies a positive infimum c after choosing a sufficiently small δ. These constants are defined by this compact class, rather than asserted to have an explicit numerical formula.

If approximating homogeneous functions in the definition lack a common Lipschitz bound, their L² limit is still the uniformly convergent Lipschitz limit of fⱼ, so the same contradiction works. For frozen minimizing blowup classes one may restrict to such minimizers and use §3.2. Varying A(x) causes bounded changes of coordinates and constants, not derivatives of A. This proves ND for quantitatively nonsymmetric, almost homogeneous balls. It does **not** prove that every point of the geometric S has that nonsymmetry at every relevant scale.

### 3.4 The annular discrete-Reifenberg sum that is actually paid

Write Δ_y(t)=Φ_y(bt)−Φ_y(at)≥0 with a,b from CB. For any geometric scale ratio θ∈(0,1), intervals (aθʲ,bθʲ) overlap at most

H=2+ceil(log(b/a)/|log θ|)

times. Thus a sum of Δ_y over a scale interval is at most H times the corresponding total Φ drop; the coefficient contribution is C times the same annular Ω increments. There is no sum of Ω(θʲ).

Here is a precise conditional centered estimate, isolating the part of the discrete Reifenberg argument that the new modulus could have broken. Let μ=Σₚrₚᵏδₚ be a finite packing measure; at scale tⱼ use a restriction μⱼ containing only atoms with rₚ≤c tⱼ. Suppose its balls have the preliminary mass bound μⱼ(B_{C tⱼ})≤Γtⱼᵏ, total mass ≤ΓRᵏ in the region used, and the hypotheses of CB at the integrated centers. Fubini and the mass bound give

Σⱼ∫ βᵏ_{μⱼ}(z,tⱼ)²dμⱼ(z)
 ≤ CΓ Σₚrₚᵏ Σ_{c′rₚ≤tⱼ≤C′R} Δₚ(tⱼ)
 ≤ CΓH Σₚrₚᵏ[Φₚ(C″R)−Φₚ(c″rₚ)]. (3.3)

Constants c′,C′,c″,C″ record the fixed truncation and annulus enlargements; the region is enlarged once accordingly. If every atom has the last drop ≤η, the right side is ≤CΓ²HηRᵏ. Taking η≤δ_DR/(CΓ²H) meets a discrete Reifenberg smallness threshold δ_DR **provided the other hypotheses have been supplied**. This is an algebraic implication, not an assertion that all stopping measures of the desired S satisfy them. It pays the Dini bookkeeping without a square-root-Dini assumption.

At comparable fixed radii, center changes can also be controlled directly. For free-boundary centers x,y with |x−y|≤c r,

|W_x(r)−W_y(r)| ≤ C[|x−y|/r+ω(|x−y|)]. (3.4)

To verify this, express the bulk term on the physical ellipsoid. Square roots/inverses/determinants are Lipschitz on the compact positive-definite matrix class. The symmetric difference of the two ellipsoids has volume at most Crⁿ[|x−y|/r+ω(|x−y|)], and the integrand is bounded by C(1+L²). On the surface, use the unit-sphere parameterization, Lip(u), u(x)=u(y)=0 and |u|≤CLr on the surfaces; include q-center and Jacobian factors. This proves (3.4) without pointwise gradient continuity. The same Ω(r) is used at every center, so it cancels in Φ_x(r)−Φ_y(r). Repeated arbitrary center shifts still need a tree argument; (3.4) alone is not a summation theorem.

### 3.5 What a complete tree would have to pay

The source tree does substantially more than (3.3). At a density level E it declares a ball good when **all** effective-stratum centers in it have small-scale density near E. Otherwise cone splitting traps its high-density points in a thin neighborhood of a (k−1)-plane. In good trees a maximal net avoids prior bad balls; their smaller balls are disjoint and their centers satisfy the small-drop condition, so the centered Reifenberg lemma bounds leaves and stops. Bad trees split low-density stops from points near the lower-dimensional plane. The latter have a small k-packing factor because their covering count is of order ρ^{1−k}, not ρ^{-k}. A stop radius η times the parent radius is needed to make density loss uniform. Alternating tree types, rather than summing independent tree estimates, controls multiplicities.

In EE §7 the constants are chosen in the order ρ<1/10 with 2c₁c₂ρ≤1/2, then γ=η′=η₁/20, then η=η₀ from the cone-splitting dichotomy. Good-tree leaf cost c₁ and bad-tree leaf cost 2c₂ρ give a geometric contraction over alternating pairs. Their covering theorem iterates only finitely many density levels, and rectifiability uses an additional local small-drop argument. Reading these endings does not establish the matrix-Dini versions of every interface.

For a future complete argument, the **whole-modulus radius cost** can be specified now. Once ε_flat, δ from (3.2), η_tree and every metric/annulus enlargement M have actually been obtained, put κ=min{ε_flat,δ,η_tree}/100 and choose the first integer j*≥1 for which

M2⁻ʲ*≤1/20, C[ω(M2⁻ʲ*)+∫₀^{M2⁻ʲ*}ω(t)dt/t]≤κ. (3.5)

Then r*=2⁻ʲ* exists by ordinary Dini. A cover of B₁ by at most Cₙr*⁻ⁿ balls of radius comparable to r* has finite cost. If local k=n−7 packing with constant K_tree were proved on those balls, its total tubular bound would be C K_tree r*⁻⁷r⁷ for r below the chart radius. Larger r are covered by |B₁.₁|≤C r*⁻⁷r⁷ after adjusting the fixed comparison factor. A density bound is C(n,λ,Λ)(1+L²)+CΩ(Mr*); if each recursion decreases the permissible density by η_tree/2, at most 2+ceil(2(E_max−E_min)/η_tree) levels are needed.

Equation (3.5) is an explicit **conditional schedule**, not a definition of a presently paid ε_flat. This report does not complete the matrix-Dini cone-splitting/tree interfaces or the geometric inclusion, and therefore does not claim a complete effective-stratum packing theorem either. It specifies which constants are paid and which do not yet exist in the argument, rather than hiding them in C(ω).

### 3.6 Ordinary Dini does not pay the available flatness iterations

The missing geometric assertion is a uniform flat-implies-C¹ theorem for the exact coefficient class. Strong compactness at a fixed scale does not prove convergence of normals through infinitely many scales. In a quadratic comparison with normalized additive energy error g(r)=Cω(Cr), one generally obtains a norm error of order √g. A model iteration

eⱼ₊₁≤θeⱼ+Cg(rⱼ)ᵃ, |νⱼ₊₁−νⱼ|≤Ceⱼ,

only bounds the sum of rotations by C[e₀+Σg(rⱼ)ᵃ]. For a=1/2, ordinary Dini does not suffice: ω(r)=log(e/r)⁻² is Dini, while Σ√ω(2⁻ʲ) diverges. De Silva–Savin's actual one-phase flatness comparison requires the additive almost-minimality error σ≤cεⁿ⁺⁴; using this interface directly produces an even smaller fractional power of ω. DET's §3 uses fractional powers and radii r^{1+α/(17n)}; §§7–9 then require τσ⁻² small. Replacing each Hölder expression by an unspecified Dini quantity does not preserve those iterations.

This is a failure of those deductions, **not** a proof that all ordinary-Dini regularity is false. Exact Euler and phase structure might yield linear ω forcing. No such complete free-boundary improvement is supplied here. Without it, a point with flat blowups cannot be removed from the geometric singular set by changing the definition of S. The non-Dini twist explains the distinction but supplies no admissible counterexample.

## 4. Route two: comparison charging only phase mismatch

This route uses the exact variational equation and calibration, rather than coordinate flattening or Weiss-density trees. It gives two estimates at the actual Dini scope and identifies the further geometric construction they would need.

### 4.1 Fixed-domain comparison has quadratic coefficient error

In any D compactly contained in {u>0}, the Euler equation is div(A∇u)=0. Let A₀=A(x₀) and h minimize the A₀-quadratic energy on D with h−u∈H¹₀(D). Testing both equations with u−h gives

∫D ∇(u−h)ᵀA₀∇(u−h)=∫D (A₀−A)∇u·∇(u−h).

Thus ||∇u−∇h||₂≤λ⁻¹||A−A₀||∞||∇u||₂, and on a domain in Bᵣ(x₀) the squared error is ≤Cω(r)²L²rⁿ. The same identity is valid on an open positive-phase subdomain using its H¹₀ variational formulation. It does not require a smooth boundary or a claim that harmonic replacement moves the phase correctly. The linear norm error here is better than the generic square-root energy-gap bound because the exact Euler equation cancels the linear variation. A harmonic replacement with this fixed domain cannot by itself improve the geometry of its boundary.

### 4.2 Fixed-flux square completion

Choose a constant vector p with pᵀA(x₀)⁻¹p=q(x₀)² and set

E_p(w;O)=∫O∩{w>0}(∇w−A⁻¹p)ᵀA(∇w−A⁻¹p),

d_p(x)=q(x)²−pᵀA(x)⁻¹p.

Since ∇w=0 a.e. on {w=0}, for every nonnegative H¹ w the exact identity is

J_{A,q}(w;O)=E_p(w;O)+∫O d_pχ_{w>0}+2∫O p·∇w.

For fixed-trace competitors the last term cancels. On O⊂Bᵣ(x₀), inverse-matrix perturbation and the bounds on p give |d_p|≤C(λ,Λ)ω(r). Minimality therefore implies

E_p(u;O) ≤ E_p(v;O)+Cω(r)|({u>0}△{v>0})∩O|. (CAL)

This charges only the **phase mismatch**, not the whole ball. It holds for all competitors in the target class, with no differentiability of A or q and no compatible coordinate map. It is a different exact comparison from RD/CB.

If, additionally, a same-trace competitor has phase mismatch confined to a slab of thickness εr in Bᵣ, the error is ≤Cω(r)εrⁿ. Young's inequality gives, for every τ>0,

Cω(r)ε ≤ τε²+C²ω(r)²/(4τ).

This would allow a quadratic remainder and potentially a linear-in-ω flatness forcing **if** one constructed a competitor contracting a coercive geometric excess, with its phase difference controlled at the same scale. That “if” is unpaid. (CAL) does not supply the competitor, contraction, control of holes, normal selection, or a sharp packing measure. Even for constant coefficients all translates of a fixed halfspace have zero E_p with the matching p; this functional alone does not locate the interface. Those translates have different traces and are not a fixed-trace counterexample, but they show why an anchored, trace-compatible geometric estimate is needed.

Neither a strong-distance estimate to an arbitrarily chosen minimizer nor ND is assumed to manufacture this missing step. An actual route to completion would prove a same-trace shape comparison, absorb the ωε term into its quadratic contraction, then sum the resulting ordinary-Dini forcing. Alternatively one would have to construct coefficients, a calibrated absolute minimizer and a geometric singular set with |Nᵣ(S∩B₁)|/r⁷ unbounded while retaining the stated common modulus and L. No such construction has been obtained. The exact coordinate subclass, non-Dini twist, its products, and logarithmic constant tuning do not satisfy that alternative.

## 5. Contribution assessment and recommendation

The complete-operation comparison is essential. The pinned dimension-seven classification plus the established constant/Hölder stratification operations already pays the usual sharp packing and rectifiability corollaries; changing the critical-dimension symbol is technical. Sobral already pays freezing/homogeneous comparison at Dini scope. I122's normalization, annular correction, covariance under ND, coordinate transport and obstruction examples are technical implementations, not a ninth finding.

The new paid continuation consists of an explicit uniform clearing iteration, compactness with phase/energy convergence and selection, ND at a quantitative symmetry scope, the annular conditional Carleson sum, fixed-radius center comparison, and the two exact comparison identities in Route two. These are elementary variational, compactness, covariance and calibration operations. No new general geometric mechanism has been completed. In particular there is no basis to claim that the **entire** Dini extension is already a routine accepted lower operation: the ordinary-Dini flatness passage and full matrix-Dini tree interfaces have not been reduced to paid source hypotheses. Conversely their being unpaid here does not establish novelty or substantiality of a future theorem.

**Recommendation: PARK Screen C in its present full scope**, preserving these bridges. A narrowly justified continuation would target the trace-compatible geometric contraction suggested by (CAL), or obtain and verify an exact ordinary-Dini flat-implies-C¹ theorem and then execute the remaining tree interfaces. Repeating full-tail charging, stronger-gauge regularity, products of the non-Dini example, or ND as an assumption would not justify another nomination. No change to R113 or the two prior screens is warranted.

## 6. Evidence and validation scope

The owned source directory contains frozen originals, separate original verdict and addendum, retrieval/extraction history, exact reading and lexical manifests, flattened inherited references, and a final inventory envelope. Only README.md, frontier/README.md, frontier/TEN-FINDINGS.md, and frontier/iterations/README.md may drift. Frozen copies never drift. Supplied recursive originals were read completely; truncated reads and the metadata failure are preserved. Relevant ledger ranges were read; no claim of reading every unrelated ledger entry is made.

The full inherited map is reused by reference: 13,223 tree entries, 749 manuscripts, 10,373 original positions (9,340 I14 plus 1,033 additional), and 776 inherited PDF-text bindings. There is no corpus copy or multiplied corpus replay. I122's exact corpus lexical occurrences remain bound; the additional focused lexical record gives exact strings, offsets and line conventions, not semantic absence. Reading ranges distinguish LF from splitlines and hash passages without an appended newline. Two new PDFs were extracted once; inherited PDFs were not re-extracted. Version HTML is preserved. Full source-operation readings are specified in the manifest; no unread external antecedent is represented as checked through its proof ending.

The verifier checks the complete exact owned inventory, flattened inherited inventories, snapshots, original-task memberships, PDFs/texts, passages, lexical memberships and all inherited corpus bytes **before executing any diagnostic source**. It intercepts inherited diagnostic requests until immutable validation finishes; each finite suite then runs once. The old corpus core is replayed once, without invoking the recursive I116 core. The verifier itself writes nothing and prohibits network, subprocesses, mutations and bytecode. Development validation and failed arguments are retained; a single final seal is created only after successful preseal validation and report completion. The seal is an inventory envelope, not a signature or self-hash.

Run from the repository:

`PYTHONDONTWRITEBYTECODE=1 python3 -B frontier/experiments/i125_dini_singular_packing/verify.py`

Finite rational diagnostics check selected recurrence, square-completion and summation identities. They certify neither the universal mathematics nor contribution status. A passing evidence replay leaves Screen C unresolved and the accepted count at eight.
