# Source365 — integrated signed-current calculation (prefreeze)

This is a durable research derivation, not a frozen nominee, manuscript, or independently reviewed theorem. The pinned joint, smooth, and measurable papers and all their operative proofs are premises stipulated true. The calculations below deliberately execute the strongest compatible consequences of the measurable paper before identifying what is still unpaid. Linearity, finite-dimensional circuit inversion, standard elliptic estimates, and approximation are credited as source/classical operations, not proposed as a substantial contribution.

## 1. Fixed geometry and the precise source interface

Write M for the pinned measurable companion. Work on its actual ball Ω=B(0,3) in R³, with its fixed rectangular toroidal cell D and two similarities S_± of ratio s=0.57. Its other parameters are L=8/5, h=0.03, a=0.81. The children have disjoint closures inside D: their outer x₁ intervals are [-1.38,-0.24] and [0.24,1.38], their x₂ extent is 0.912 and x₃ extent 0.57; the parent's central x₁ half-width is 0.048. The strict margins in M's geometry lemma are the compatibility certificate. In particular 2s=1.14>1 and 2s³=0.370386<1 hold simultaneously for these actual cells. No freedom to vary s through an arbitrary regime is asserted.

Let D_ν=S_νD, B_ν=D_ν minus its two closed children, Σ_ν=∂D_ν, and μ_ν the probability surface measures transported as in M. Let γ be M's fixed scalar conductivity, equal to the single block coefficient b₀ after similarity on every B_ν and to 1 elsewhere. It has constants 0<c≤γ≤C<∞ and equals 1 in a fixed outer collar. The B_ν are pairwise disjoint up to null sets. The Cantor set K=intersection_N union_|ν|=N closure(D_ν) has zero volume by 2s³<1. No regularity of γ beyond bounded measurability is introduced.

M, labels nu:source-lemma, nu:source-identity, nu:source-bounds, proves the following exact interface. For p=(p₀,p₋,p₊) in the plane P={sum p_i=0}, there is a canonical linear choice W_p, obtained by inverting the block voltage/current map and setting its outer voltage to zero. Put W_{ν,p}(x)=s^{-|ν|}W_p(S_ν^{-1}x), extending by zero outside D_ν. Then W_{ν,p}∈H¹₀(Ω)∩L∞, is constant inside each child, and

E_γ(W_{ν,p},ψ)=p₀ m_ν(ψ)+p₋ m_{ν-}(ψ)+p₊ m_{ν+}(ψ),       (1)

for every ψ∈H¹(Ω), where E_γ(v,ψ)=∫γ∇v·∇ψ and m_ν(ψ)=∫_{Σ_ν}Tr ψ dμ_ν. Also

||W_{ν,p}||∞≤C_W s^{-|ν|}|p|,
∫|∇W_{ν,p}|²≤C_W s^{-|ν|}|p|².                            (2)

The scaling s^{-j} is voltage scaling in dimension three, not a change in ellipticity. The vector p is an integrated current, and the pushforward measures on each shared surface agree exactly. These facts are essential to telescoping.

The map p↦W_p is linear because both the PDE and the finite-dimensional inverse with outer voltage zero are linear. Define the symmetric bilinear form R on P by R(p,q)=E_γ(W_p,W_q). It is positive definite: zero energy implies a constant block voltage, hence zero after outer normalization and then p=0. Since P has dimension two, there are actual constants 0<r_-≤r_+<∞ with

r_-|p|²≤R(p,p)≤r_+|p|².                                  (3)

These constants depend on the constructed block; no numerical effective values are claimed.

The gradient of W_{ν,p} is supported in B_ν. Thus distinct node potentials are exactly energy-orthogonal, including ancestor/descendant nodes. At one node similarity gives

E_γ(W_{ν,p},W_{ν,q})=s^{-|ν|}R(p,q).                       (4)

M's equal-average lemma says every γ-harmonic u∈H¹ has one common value m_ν(u)=u_* at all nodes. For bounded u, |u_*|≤||u||∞. This is a surface-trace assertion, not a pointwise trace theorem on K.

## 2. General conserved charges and convergence

Let X={-,+}^N with product Bernoulli probability μ. Nested cells give a continuous one-to-one coding π:X→K, since their diameters tend to zero and sibling closures are disjoint. For a cylinder [ν], μ([ν])=2^{-|ν|}. For real f∈L∞(X,μ) with ∫f dμ=0 set

q_ν=∫_[ν] f dμ,  q_empty=0,
p_ν=(-q_ν,q_{ν-},q_{ν+})∈P.

Conservation q_ν=q_{ν-}+q_{ν+} is exact. At level j,

max_|ν|=j |q_ν|≤2^{-j}||f||∞,
Σ_|ν|=j |q_ν|≤||f||₁,
Q_j:=Σ_|ν|=j q_ν²≤2^{-j}||f||₂².                         (5)

Define Z_j(f)=Σ_|ν|=j W_{ν,p_ν} and T_N f=Σ_{j=0}^{N-1}Z_j(f). Since cells at a level are disjoint, the L∞ norm uses a maximum, not a sum over 2^j terms. Equations (2)–(5), with λ=(2s)^{-1}<1, yield

||Z_j(f)||∞≤C λ^j||f||∞,
E_γ(Z_j(f),Z_j(f))≤C λ^j||f||₂².                          (6)

All different levels are also energy-orthogonal by (4). Therefore T_N f converges in H¹₀ and L∞ to a linear Tf, and

||Tf-T_Nf||∞≤C λ^N/(1-λ) ||f||∞,
E_γ(Tf-T_Nf,Tf-T_Nf)≤C λ^N/(1-λ)||f||₂².                 (7)

Poincaré controls the full H¹ norm. In particular Tf is supported in closure(D). These are rigorous uniform tail estimates; no pointwise representative of f is used.

For each finite N, cancellation of shared measures in (1) gives

E_γ(T_Nf,ψ)=Σ_|ν|=N q_ν m_ν(ψ).                          (8)

For smooth ψ, pick x_ν∈closure(D_ν). The difference between the right side and Σ q_ν ψ(x_ν) has absolute value at most diam(D)s^N ||∇ψ||∞||f||₁. The latter sum tends to ∫_X f(ω)ψ(π(ω))dμ(ω), with the same error bound. Consequently

E_γ(Tf,ψ)=∫_X f(ω)ψ(π(ω))dμ(ω), ψ∈C_c∞(Ω).             (9)

Thus -div(γ∇Tf)=π_*(fμ) as distributions. Its total charge is zero; it is generally a nonzero interior source. We never assert that Tf is globally γ-harmonic. Equation (9) is also a certificate that these measures belong to H^{-1} in this constructed geometry.

The map T is injective. If Tf=0, choose, for each cylinder [ν], a smooth test equal to one on closure(D_ν) and zero near all other cells at depth |ν|. Positive separation of the finite set of cells gives such a test. Equation (9) implies q_ν=0 for every ν. Cylinder functions are dense in L² (or simple cylinder partitions approximate measurable sets), so all conditional expectations of f vanish and f=0 a.e. This proof distinguishes actual coefficients later; it does not count a redundant parametrization as nonuniqueness.

## 3. Exact energy and the martingale scale

For real f,g∈L²₀(X), the same energy convergence (without claiming L∞ convergence) defines Tf,Tg∈H¹₀. From (4),

E_γ(Tf,Tg)=Σ_ν s^{-|ν|}R(p_ν(f),p_ν(g)).                 (10)

This is the exact formula. It does not assume that the block is symmetric under exchange of children. In particular it does not replace R by a diagonal matrix without justification.

Let E_jf denote conditional expectation on depth-j cylinders and d_jf=E_jf-E_{j-1}f. Then Q_j=2^{-j}||E_jf||₂². Summing |p_ν|² over depth j gives Q_j+Q_{j+1}, so

Σ_ν s^{-|ν|}|p_ν|²
 =(1+s)Σ_{j≥1}λ^j||E_jf||₂²
 =(1+s)/(1-λ) Σ_{k≥1}λ^k||d_kf||₂².                     (11)

The last equality follows by orthogonality of martingale differences and Tonelli for nonnegative terms. Combining (3), (10), and (11) proves two-sided energy equivalence with this weighted square sum, with lower and upper constants respectively r_-(1+s)/(1-λ) and r_+(1+s)/(1-λ). Formula (10) remains the exact identity; (11) is an equivalence after inserting the bounds on R.

This establishes more than the single opposite-charge example, but it is ordinary Hilbert-space accounting on the source's exact linear block. The completion of the weighted martingale space can contain distributions that are not finite measures; we do not apply the nonlinear conductivity transformation to that completion.

There is also a sufficient Lᵖ regime. For p≥2,

|q_ν|≤2^{-j(1-1/p)}||f||ₚ.

If a_p:=s^{-1}2^{-(1-1/p)}<1, then ||Z_j(f)||∞≤C a_p^j||f||ₚ, and the H¹ estimates still follow from ||f||₂≤||f||ₚ. Thus T:Lᵖ₀→H¹₀∩L∞ is bounded for

p>p_c:=log(2)/log(2s)≈5.2901.

The number d=log(2)/log(1/s) satisfies p_c=d/(d-1), but no geometric regularity theorem is being inferred from that notation. This is a sufficient summability threshold, not a proved sharp endpoint. At p=p_c this estimate is not summable, and no counterexample or endpoint assertion follows. Compatible nonzero examples exist: any nonzero bounded cylinder function of mean zero belongs to every such Lᵖ space.

For p>p_c, T takes bounded Lᵖ sets to relatively compact sets in H¹∩L∞. Indeed finite T_N has finite-dimensional range and uniformly bounded coefficients, and the tails are uniformly small by (7) and its a_p analogue. This compact injective map has no bounded inverse on its infinite-dimensional range. In particular the parametrization below is not asserted to be an embedded Banach submanifold of L∞.

## 4. Exact nonlinear iso-data family on the same base coefficient

Fix p>p_c, including p=∞, and choose a radius ε₀>0 with ||Tf||∞≤1/2 whenever ||f||ₚ<ε₀. Set

ρ_f=1+Tf,              γ_f=γρ_f².                         (12)

Then c/4≤γ_f≤9C/4 and γ_f=1 in the same fixed outer collar. The map f↦γ_f is a polynomial analytic map Lᵖ₀→L∞. It is injective: γ_f=γ_g implies ρ_f²=ρ_g² a.e.; both are positive, so Tf=Tg and then f=g. Its derivative at zero is 2γTf, an injective compact map. All these conductivities are in the source's bounded measurable scalar class, without an additional smoothness claim.

For bounded γ-harmonic u and smooth compactly supported φ, use (8) with ψ=(u-u_*)φ. This product is H¹ and has compact support. Since each surface average of u-u_* vanishes,

|Σ_|ν|=N q_ν ∫_{Σ_ν}(Tr u-u_*)φ dμ_ν|
 ≤2||u||∞ diam(D)s^N ||∇φ||∞ ||f||₁ →0.

The strong H¹ convergence permits passage to the fixed product test. Therefore

E_γ(ρ_f,(u-u_*)φ)=0.                                    (13)

For smooth boundary input F, the weak maximum principle bounds its γ-harmonic extension u. Define

u_f=u_*+(u-u_*)/ρ_f.

Bounded Sobolev product and chain rules give u_f∈H¹, and u_f=u near the outer boundary. Direct computation, with no multiplication of weak limits, gives the L² flux identity

γ_f∇u_f=ρ_f γ∇u-(u-u_*)γ∇ρ_f.                           (14)

Test the equation for u by ρ_fφ; expand (13); subtraction proves that (14) has zero divergence. Density of compact smooth tests gives the full weak equation. Ellipticity and the prescribed boundary trace give uniqueness.

For an arbitrary second trace G∈H^{1/2}(∂Ω), take any bounded right-inverse extension into H¹, then multiply it by a smooth cutoff supported in the common outer collar and equal to one near ∂Ω. Its gradient is supported where the two fluxes coincide. Hence the variational boundary pairings agree. Energy bounds and density extend from smooth F to all F∈H^{1/2}(∂Ω):

Λ_{γ_f}=Λ_γ in L(H^{1/2}(∂Ω),H^{-1/2}(∂Ω)).              (15)

No boundary regularity of u beyond the variational trace is used. Restricted same-patch maps agree as a consequence of (15); this argument does not obtain the full map from partial data.

There are infinitely many independent parameter directions already on one fixed γ and one fixed tree. For example, mean-zero cylinder Haar functions at arbitrarily many depths give independent f and, by injectivity, independent first variations. This contains the source's one-parameter example and its finite choices. The extra parametrization follows from the source's linear block and weighted identity; it is therefore credited as a compatible paid consequence, not nominated by its infinite-dimensional wording.

These coefficients are distinct in fixed coordinates. They are also inequivalent under the usual smooth boundary-fixing diffeomorphism ambiguity for scalar conductivity tensors: if Φ_*(γ_f I)=γ_g I, then

γ_f(x)DΦ(x)DΦ(x)^t/|det DΦ(x)|=γ_g(Φ(x))I

a.e., so DΦDΦ^t is scalar a.e. and then everywhere by smoothness. Thus Φ is a smooth Euclidean conformal diffeomorphism. The smooth companion's conformal rigidity argument, fixed on a boundary patch, makes Φ the identity (in particular when fixed on the whole sphere). Equation (12) and injectivity then imply f=g. This assertion concerns smooth diffeomorphisms; no classification of arbitrary Sobolev homeomorphisms is claimed. There is no unitary-connection gauge acting on the scalar coefficient in (12).

For completeness, the standard Fréchet derivative of the full boundary map is compatible with this family. If h∈L∞ and γ+th stays positive, subtract the two weak equations to obtain ||∇(u_t-u)||₂≤C|t| ||h||∞||F||_{H^{1/2}}. The variational difference identity then gives

⟨DΛ_γ[h]F,G⟩=∫h∇u^F·∇u^G,

with an operator-norm O(t²||h||∞²) remainder on bounded perturbations. Differentiating the exact constant map (15) proves DΛ_γ[2γTf]=0. For smooth inputs the same identity also follows directly from (13) with products; the derivative argument handles all H^{1/2} inputs without assuming that their solutions are bounded. An infinite-dimensional linearized kernel here concerns a rough γ, not the smooth joint problem.

## 5. Smoothing: strongest compatible forward bound, exact spaces

Fix a compact interior K₀ containing closure(D), with distance d₀>0 from ∂Ω. Let a₁,a₂ be any scalar conductivities with common ellipticity bounds α,β and a₁=a₂ outside K₀. The boundary pairing is the density/energy pairing, with norm H^{1/2}(∂Ω)→H^{-1/2}(∂Ω).

Meyers' original 1963 proof supplies an exponent q>2 and an interior estimate for homogeneous solutions, depending only on dimension and ellipticity (and the interior distance after covering). Its mechanism is the near-2 bounded inverse for the Laplacian, interpolation of its norm with value 1 at 2, perturbative absorption of I-A/β, localization by cutoff, Sobolev improvement and iteration. In the scalar symmetric case the matrix remainder from the general proof is absent. On the fixed K₀ a finite covering by interior balls gives

||∇u_i^F||_{L^q(K₀)}≤C(α,β,Ω,d₀,q)||F||_{H^{1/2}}.     (16)

The global H¹ estimate used here follows by a bounded trace extension and testing the zero-trace remainder; the L² term in the interior estimate is bounded by the same H¹ estimate. No differentiability of a_i is assumed. Caccioppoli, when needed in this localization, follows by testing with η²(u-c) and absorbing 2βη|u-c||∇u||∇η| using α|η∇u|²/2.

The exact variational difference identity is

⟨(Λ_{a₁}-Λ_{a₂})F,G⟩=∫_{K₀}(a₁-a₂)∇u₁^F·∇u₂^G.       (17)

To derive it, use u₂^G as extension in the first pairing and symmetry plus the zero-trace weak equations in the second. Let r=q/(q-2), θ=1/r. Hölder and (16) give

||Λ_{a₁}-Λ_{a₂}||≤C||a₁-a₂||_{L^r(K₀)}
 ≤C(2β)^{1-θ}||a₁-a₂||_{L¹(K₀)}^θ,  θ=(q-2)/q>0.        (18)

This is a uniform forward continuity estimate for the stated common-collar class, not an inverse stability estimate. It is stronger than just strong-operator convergence under homogenization. There is no claim of a sharp q, explicit numerical exponent, or collar-independent constant.

There is also an elementary independent qualitative proof of the needed operator-norm convergence. For fixed a, the map F↦∇u_a^F|K₀ is compact from H^{1/2} to L²: a weakly null bounded sequence of inputs gives weak H¹ convergence to zero by uniqueness, strong interior L² convergence by Rellich, and then strong interior gradient convergence by Caccioppoli. Bounded multiplication by a_n-a tends strongly to zero on L² if a_n→a in measure. Strong convergence is uniform on a compact set, by a finite-net argument. In (17) bound the other gradient in L² uniformly. This proves ||Λ_{a_n}-Λ_a||→0 whenever differences have the fixed compact support and ellipticity is uniform. Thus the smoothing conclusion below does not depend on extracting a numerical Meyers exponent.

Extend γ_f by 1 outside Ω and convolve with a nonnegative smooth compactly supported approximate identity of radius t, denoting the result a_{f,t}. For all sufficiently small t, a_{f,t}=1 on a common smaller outer collar, is smooth, scalar, and retains the common positive bounds. As t→0 it converges to γ_f in every finite Lᵐ, by translation continuity and dominated approximation. Applying (18),

||Λ_{a_{f,t}}-Λ_γ||≤C||a_{f,t}-γ_f||₁^θ →0.              (19)

For fixed distinct f,g and any finite m≥1, the triangle inequality gives

||a_{f,t}-a_{g,t}||_m→||γ_f-γ_g||_m>0,
||Λ_{a_{f,t}}-Λ_{a_{g,t}}||→0.                           (20)

Thus smooth scalar same-collar conductivities with only ellipticity bounds admit no uniform inverse modulus from the full operator norm to Lᵐ. The smooth uniqueness premise ensures that the two full maps cannot be exactly equal once the smoothed coefficients are distinct. No finite-stage exact smooth nonuniqueness has been inferred.

One can prescribe any positive noise sequence η_k↓0 and select t_k↓0 so that the data distance in (20) is ≤η_k and the coefficient separation is ≥one half its limiting value. This is a justified diagonal choice, not an effective relation between η_k and a smoothing radius. The L∞ coefficient class supplies no uniform translation modulus for γ, and the block's Baire scalarization supplies no such modulus either.

This works uniformly over a bounded Lᵖ parameter ball with p>p_c: by the finite-dimensional approximants and uniform tails above, the set of potentials is relatively compact in L∞, and so is the associated set of γ_f. Its closure remains within the same ellipticity class. Compactness in L¹ and the contraction property of convolution give uniform L¹ approximation on the whole set via a finite net. Equations (18)–(19) then give a single small t for a prescribed uniform data error. Again the existence of that t is qualitative. There is no lower bound on separation uniform over all different parameters; T is compact.

Any finite collection of bounded boundary pairings, with input/test norms controlled, has error at most its norm bound times (19). This is approximate indistinguishability for such measurements. It is not exact equality of finitely many scalars after smoothing, and it gives no noisy inverse theorem for the joint metric/connection problem.

## 6. Joint problem: compactness and finite measurements carried through

This section is a comparison reduction within Source365, not a second nominee. It tests the source's smooth metric/connection theorem against the strongest standard compactness consequence, on a class whose purported free parameters actually exist.

Fix a smooth compact connected M, a fixed nonempty proper open patch Γ, a reference smooth metric for Sobolev norms and the given trivial Hermitian rank-two bundle/trivialization. For each smooth metric g and unitary connection A, use the density-valued energy pairing

E_{g,A}(u,v)=∫_M g^{ij}⟨(∂_i+A_i)u,(∂_j+A_j)v⟩ dV_g.

Take the same-patch input/test normed space X_Γ=H^{1/2}_{co}(Γ;C²) with the inherited H^{1/2} norm, and its dual output; no full-boundary data are being substituted. A fixed bounded trace extension on the whole boundary restricts to an extension of every element of X_Γ; it need not preserve support inside M. Zero extension on the boundary is already part of the source definition. The bilinear restrictions are evaluated only on the prescribed traces. Compactly supported smooth inputs remain sufficient to detect equality by the source theorem. This argument does not demand that X_Γ itself be a closed subspace.

On a class with uniformly equivalent metrics and uniformly bounded A, the zero-trace energy is uniformly coercive in H¹. Indeed the unitary connection gives |d|u||≤|d_Au| a.e.; the scalar Poincaré inequality for |u| with zero trace controls ||u||₂. Then du=d_Au-Au controls ||du||₂. The reverse energy bound is immediate. A fixed trace extension and the weak equation give ||u^F_{g,A}||_{H¹}≤C||F||_{H^{1/2}}.

If two pairs are close in C⁰, expand each energy using d_{A₂}u=d_{A₁}u+(A₂-A₁)u. Coefficient differences in g^{-1}dV_g and in A, with the boundedness above, give

|E_{g₁,A₁}(u,v)-E_{g₂,A₂}(u,v)|≤Cε||u||_{H¹}||v||_{H¹},
ε=||g₁-g₂||_{C⁰}+||A₁-A₂||_{C⁰}.

The difference of the weak equations, or the two-solution variational identity, therefore proves

||D(g₁,A₁)-D(g₂,A₂)||_{L(X_Γ,X_Γ^*)}≤Cε.                (21)

All matrix products retain their order in this expansion; no commutation of A_i is assumed. This is only forward continuity on a prescribed fixed class and fixed patch.

For an arbitrary compact set K of smooth pairs (compact in C⁰, with every member including every limit still smooth), define R⊂K×K by equality of their same-patch data. It is closed by (21). Source365 identifies R exactly with the relation “related by a smooth diffeomorphism and unitary gauge fixed on Γ,” with its specified pullback/gauge action. Thus K/R is compact Hausdorff, and the induced map into the normed data space is a homeomorphism onto its compact image. This does not prove a compact gauge slice for a given coefficient norm ball. It assumes an actual compact K of smooth pairs. Nor does it provide a useful numerical modulus or a reconstruction algorithm.

One concrete metric statement avoiding a spurious orbit-distance claim is this. Give K a fixed compatible coefficient metric d_K and let dist((P,Q),R) use the product metric. Set ω(t)=sup{dist((P,Q),R):P,Q∈K,||D(P)-D(Q)||≤t}. Compactness gives ω(t)→0: otherwise a sequence with data differences tending to zero has a limiting pair in R while staying a positive distance from R. This says that the pair lies near some equivalent pair within K. It is not automatically a bound on the distance of Q to the orbit of the fixed P in an ambient coefficient norm.

Here is an actual injectively parametrized compact class, so the inverse parameter modulus is less vacuous. Let M=S¹×closed(B^{n-1}) for n≥3, with a fixed smooth product metric g₀ and a fixed proper patch Γ. Write θ for the angular coordinate of period 2π and dθ for its globally defined smooth closed one-form. On the trivial C² bundle set

g_τ=e^{2τ}g₀,       A_σ=iσ dθ I₂,
(τ,σ)∈Q=[0,1/10]×[1/20,1/10].                           (22)

These are smooth unitary connections and positive smooth metrics; Q maps to a compact set in every Cᵏ norm. There is no unknown-topology claim. The parameters are not forced by each other. The volume is e^{nτ}Vol(g₀), invariant under diffeomorphism, so equivalence forces τ=τ'. For a loop generating π₁(M)=Z, the parallel-transport equation V'=-iσV has holonomy e^{-2πiσ}I₂. A diffeomorphism acts on π₁ by ±1, and a gauge conjugates holonomy (a Γ-fixed gauge is the identity at a chosen basepoint in Γ). Thus equivalence requires σ=±σ' modulo integers. The interval [1/20,1/10] makes this possible only when σ=σ'. Both parameters therefore vary independently through inequivalent pairs. This explicitly checks the compatibility and nonempty-regime issue.

Consequently F:Q→L(X_Γ,X_Γ^*), F(τ,σ)=D(g_τ,A_σ), is continuous and injective by the source theorem. For each ε>0 for which the separated-pair set is nonempty, compactness yields

m(ε)=min_{|z-z'|≥ε}||F(z)-F(z')||>0.                    (23)

This is an abstract inverse modulus; no lower bound for m(ε) is supplied by uniqueness. It does not quantify the source's shrinking/angular/matrix constants.

There is even a finite-measurement consequence at each fixed ε, and it is also standard. For every pair |z-z'|≥ε the source equality criterion implies that some smooth compactly supported traces f,h on Γ have a nonzero complex pairing ⟨(F(z)-F(z'))f,h⟩. Normalize their H^{1/2} norms to at most one. Continuity preserves a positive absolute lower bound on a neighborhood of this pair. A finite subcover of the compact separated-pair set yields finitely many fixed pairs (f_j,h_j), all in C_c∞(Γ;C²), and a δ>0 such that

max_j |⟨(F(z)-F(z'))f_j,h_j⟩|≥δ whenever |z-z'|≥ε.       (24)

Each chosen support has its own positive distance from the patch edge; their finite union still lies compactly in Γ. There is no claim of an a priori support margin uniform in ε, a number of measurements bounded in terms of ε, or one finite family that works at all resolutions. Complex readings may equivalently be split into real and imaginary scalars.

To make the associated approximate recovery concrete, write B(z) for the finite vector of pairings in (24). Uniform continuity gives a finite parameter net such that every z has a net point v with ||B(v)-B(z)||∞<δ/4. Given readings y with ||y-B(z_true)||∞<δ/4, select a net point minimizing ||B(v)-y||∞. A near true net point gives residual <δ/2, so the selected point satisfies ||B(v)-B(z_true)||∞<3δ/4 and hence |v-z_true|<ε by (24). This is a finite search once the witnesses, δ and net are known. Their existence proof does not compute them from the source, bound their complexity, or supply an effective noisy recovery theorem.

Thus qualitative inverse continuity, independent metric/holonomy parameters, finite measurements at any prescribed fixed resolution, and a conditional finite-net search are already compatible routine consequences. They are all credited as paid. A substantial quantitative extension would have to go beyond (23)–(24) by controlling these quantities from explicit a priori geometry/coefficient/patch bounds or by proving another new operation; it cannot count the compactness construction itself.

## 7. What has and has not been paid

All three source headlines are premises. M already contains the essential nonsmooth scalarization, synchronized two-field construction, exact block Cauchy data, infinite geometry, nonzero interior-source potential, and nonlinear transformation. It already gives an interval of perturbation amplitudes and finite multiple-site families. Sections 1–4 above use their actual strongest compatibility; their new bookkeeping does not manufacture an unpaid operation. Meyers plus the elementary difference identity and smoothing pay Section 5. Earlier conformal-gauge algebra in Daudé–Kamran–Nicoleau is compatible, but its full-boundary harmonic factor would be trivial; our source potential is deliberately not harmonic, and (13) is the precise replacement.

No derivative regularity of γ_f follows from Tf∈H¹∩L∞: multiplication by the original γ retains its uncontrolled roughness. The sufficient p-threshold controls parameter-to-potential boundedness, not a new conductivity regularity class. An exact pair in a stronger coefficient class would require a compatible quantitative refinement of the finite-field scalarization/block construction, preserving positivity, scalar isotropy, collar, all Cauchy identities, and limiting charge cancellation. None is proved here.

For the smooth joint problem, a noisy extension still requires quantitative control of the actual matrix product extension, point-distribution/jet surjectivity, harmonic-frame conditioning, separation scale, shrinking-sphere errors and displacement/prolongation propagation, all after a specified gauge/diffeomorphism normalization. Pointwise uniqueness gives none of those uniform constants. The smooth scalar partial stability paper read here uses a uniform W^{2,∞} bound, a fixed known exterior, and a lower accessible-patch size; its double-variable propagation proof cannot be imported to an arbitrary unknown joint metric/connection by a change of notation.

For arbitrary topology or bundles, the primary real-analytic Green-kernel embedding proof genuinely glues fibre maps and recovers the base, but uses analytic continuation both to continue image graphs and to identify the connections. Its arbitrary rank/topology is already paid at analytic hypotheses. The joint smooth rank-two paper requires the stated trivial bundle and fixed manifold/boundary identification. No nontrivial-bundle or arbitrary-rank smooth extension has been proved here.

The disposition is therefore PREFREEZE/no nominee. There is no frozen candidate to narrow later, no correctness/contribution grade, and no acceptance/count claim. The retained derivations include a completed integrated construction, rather than merely a catalogue choice or a named hard gap. They do not establish exhaustion or worldwide priority.
