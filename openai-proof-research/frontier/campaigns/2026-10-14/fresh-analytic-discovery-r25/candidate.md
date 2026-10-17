# W5: bounded higher-codimension coordinates for a pinched threefold

Myeongjin Kang. No affiliation. Original prose CC BY 4.0.

Status: author deduction for the unchanged target in original-scope.md; no independent proof or contribution verdict, no count. The pre-freeze feasibility chronology is in freeze-receipt.json. All source results below are stipulated true at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. This is not an upstream correctness audit.

## 1. Full statement

There exist a nonempty contractible domain M⊂C³, a smooth geodesically complete Kähler metric g on M, and constants 0<A≤B<∞ such that −B≤K_g(σ)≤−A for every real tangent two-plane, together with a bounded holomorphic embedding F:M→C⁵, while every bounded holomorphic G:M→C³ has a point where det dG=0.

Here an embedding is an injective holomorphic immersion and a homeomorphism onto its image with the subspace topology. No properness into C⁵, optimal target dimension, C⁴ obstruction, or comparison of the Carathéodory metric is asserted.

## 2. Exact source interface

Use the pinned manuscript *A negatively pinched Kähler threefold without bounded holomorphic coordinates*, with the following notation and results.

The base is B²={z∈C²:|z|<1}; ψ(z)=−log(1−|z|²). Sections 3,5,6 supply fixed numbers a>0, ε>0, an integer Q≥4 and homogeneous holomorphic polynomials P_j=P_{Q^j} with

(2.1)  P_j(0)=0, and |P_j(z)|≤C_P |z|^{Q^j} on C²,

and regularized logarithms

(2.2)  U_j(z)=log((|1−aP_j(z)|²+ε²)/(1+ε²)).

The source Lemma `base:convergence` asserts local C∞ convergence of ΣU_j, and its Lemmas `base:minorant` and `base:chart-estimates` say that for every fixed finite L above the explicit threshold 5log(Q)/d₃, the potential

(2.3)  φ=ψ+L Σ_j U_j

has the controlled positive Hessian and centered-chart jets required by Proposition `metric:transfer`, and has no pluriharmonic minorant with the logarithmic allowance in Proposition `base:existence`. In particular choose and fix an INTEGER L>5log(Q)/d₃. This is a permitted source parameter choice, not a change to a frozen target or an improvement of the source's parameter estimates. The source chooses the metric parameter only afterward.

Set

(2.4)  M={ (z,w)∈B²×C : e^{φ(z)}|w|²<1 }.

Proposition `metric:transfer` supplies a smooth complete Kähler metric on this same M with two finite uniform negative real-sectional bounds; it also supplies contractibility. Lemma `map:obstruction` says every bounded holomorphic M→C³ has a Jacobian zero. These are credited source conclusions. They will remain valid when extra holomorphic functions are constructed on the already fixed M.

The new obligation is to construct the bounded C⁵ embedding. The rest of the proof does not use curvature estimates, representing measures, or a Jensen inequality.

## 3. A weighted family of scalar infinite products

Put

c₀=a/(1+ε²),  κ=(1+ε²)²/(a²ε²),  ρ=c₀/2,  η_j=2^{−j} (j≥1).

For t∈D_ρ={t∈C:|t|<ρ}, let c_j(t)=c₀+η_j t. These numbers are nonzero: |c_j(t)|≥c₀−ρ/2>0. Define formally

(3.1)  q_t(z)=∏_{j=1}^∞ [1−c_j(t)P_j(z)].

For every compact K⊂B², choose r<1 with |z|≤r on K. Equation (2.1) gives

Σ_j sup_{z∈K,t∈D_ρ}|c_j(t)P_j(z)| ≤ (c₀+ρ) C_P Σ_j r^{Q^j}<∞.

For example Q^j≥j, so the final series is bounded by Σ_j r^j. The usual finite-product expansion bound ∏(1+u_j)≤exp(Σu_j), u_j≥0, shows the products in (3.1) converge uniformly on K, uniformly over these t. Their limit is holomorphic in z, with q_t(0)=1.

For each fixed z and t the product is zero IF AND ONLY IF one of its factors is zero. The reverse direction is immediate. For the forward direction, if no factor vanishes, choose J so |c_j(t)P_j(z)|≤1/2 for j≥J. The analytic logarithm log(1−u)=−Σ_{m≥1}u^m/m on |u|<1 satisfies |log(1−u)|≤2|u| in this disk. Thus the tail is the exponential of an absolutely convergent series and is nonzero. The finitely many preceding factors are nonzero as well.

The essential global estimate is obtained without replacing ε-regularization by an unregularized logarithm. For every c,P∈C, Cauchy–Schwarz applied to

1−cP=(c/a)(1−aP)+((1−c/a)/ε) ε

gives

(3.2)  |1−cP|² ≤ (1+κ|c−c₀|²) (|1−aP|²+ε²)/(1+ε²).

Indeed, direct completion of the square yields the exact coefficient identity

(1+ε²)(|c/a|²+|1−c/a|²/ε²)=1+κ|c−c₀|².

Apply (3.2) to the first N factors. Since |c_j(t)−c₀|=η_j|t|,

|∏_{j≤N}(1−c_j(t)P_j(z))|²
 ≤ exp(κ|t|² Σ_{j≤N}η_j²) exp(Σ_{j≤N}U_j(z)).

Pass to the limit at each z, using the proved convergence of the product and the source convergence of the logarithmic series. Since Σ_{j≥1}η_j²=1/3,

(3.3)  |q_t(z)|² ≤ C₀ exp(Σ_j U_j(z)),  C₀=exp(κρ²/3),

uniformly for every z∈B² and t∈D_ρ. This is a GLOBAL bound; it does not come from compact-open control alone.

The choice c₀ matters: its per-factor Cauchy–Schwarz loss is exactly one. A fixed nonzero perturbation at infinitely many indices would accumulate a divergent constant. Square-summable perturbations keep the total loss finite while leaving each individual factor movable.

## 4. Three products have no common zero

We now select t₁,t₂,t₃∈D_ρ so that q_{t₁},q_{t₂},q_{t₃} have no common zero in B². Only classical algebraic dependence and Baire category are used for this selection.

For every ordered triple J=(j₁,j₂,j₃) of positive integers, three polynomials P_{j₁},P_{j₂},P_{j₃} in two complex variables satisfy a nontrivial polynomial relation

(4.1)  R_J(P_{j₁}(z),P_{j₂}(z),P_{j₃}(z))=0 on C²,

where R_J∈C[X₁,X₂,X₃] is not the zero polynomial. For completeness, let D be at least one and at least the three degrees. The monomials in these three polynomials of total degree ≤m number binom(m+3,3), whereas they lie in the vector space of two-variable polynomials of degree ≤mD, of dimension binom(mD+2,2). The first quantity exceeds the second for large m, yielding a nontrivial relation. This also handles repeated indices or identically zero polynomials.

On the parameter polydisk T=D_ρ³, form

(4.2)  H_J(t₁,t₂,t₃)=R_J(1/(c₀+η_{j₁}t₁), 1/(c₀+η_{j₂}t₂), 1/(c₀+η_{j₃}t₃)).

This is holomorphic. It is not identically zero: each of its three rational coordinate substitutions maps D_ρ biholomorphically onto a nonempty open subset of C, so their product has open image in C³; a nonzero polynomial cannot vanish on that image. Thus {H_J=0} is closed relative to T and has empty interior. The polydisk T is a Baire space (it is an open subset of finite-dimensional Euclidean space, hence locally compact Hausdorff). There are countably many ordered triples J. Choose

(4.3)  (t₁,t₂,t₃) ∈ T \ ⋃_J {H_J=0}.

If the three selected products vanished at some z∈B², the zero characterization in §3 would give an index j_l with P_{j_l}(z)=1/(c₀+η_{j_l}t_l) for each l=1,2,3. Substituting into (4.1) would imply H_J(t₁,t₂,t₃)=0, contradicting (4.3). This proves the asserted common-zero exclusion on the ENTIRE ball, not just a compact subset.

The role of three is dimension-theoretic. No claim that two products can avoid common zeros is made. Generic finite generation is a classical operation and is credited explicitly in the comparison record.

## 5. Weighted sections and the embedding

Let q_l=q_{t_l} and f_l=q_l^L, l=1,2,3. The integer choice of L makes these single-valued holomorphic functions, including at their zeros. They have no common zero and, by (2.3) and (3.3),

(5.1)  |f_l(z)|² ≤ C₀^L exp(L Σ_jU_j(z))
                   = C₀^L exp(φ(z)−ψ(z)).

Define

(5.2)  F(z,w)=(z₁,z₂,w f₁(z),w f₂(z),w f₃(z)).

This map is holomorphic. If (z,w)∈M, then (2.4),(5.1) give

(5.3)  |w f_l(z)|² < C₀^L exp(−ψ(z))=C₀^L(1−|z|²).

Consequently |F(z,w)|²≤|z|²+3C₀^L(1−|z|²)≤max(1,3C₀^L), so F has bounded Euclidean image.

Injectivity: if F(z,w)=F(z',w'), its first two components give z=z'. Some f_l(z) is nonzero, so comparison of the corresponding fiber component gives w=w'.

Immersion: for a tangent vector (u,v)∈C²×C in the kernel of dF, the first two components give u=0. The last three then give v f_l(z)=0 for each l; the common-zero exclusion forces v=0. Thus dF has complex rank three everywhere.

Topology of the inverse: on the open base set O_l={z:f_l(z)≠0}, the inverse from F(M∩(O_l×C)) is explicitly

(Z₁,Z₂,Y₁,Y₂,Y₃) ↦ ((Z₁,Z₂),Y_l/f_l(Z₁,Z₂)).

The subset where (Z₁,Z₂)∈O_l is relatively open in F(M), and this formula is continuous there (indeed holomorphic on its ambient open coordinate domain). These three patches cover F(M) and the inverse formulas agree on overlaps by injectivity. Hence F is a homeomorphism onto its image. This proves it is a holomorphic embedding in the full frozen sense.

## 6. Completion of the full conjunction

The potential, domain, and source metric were fixed in §2 before selecting any of the t_l. The new functions do not modify any source parameter or curvature estimate. Thus the same M has the source's contractibility, complete smooth metric and two-sided negative sectional pinching, its source obstruction to every bounded C³ map of full rank everywhere, and the bounded C⁵ embedding just proved. M is nonempty because (0,0)∈M. This proves the full statement in §1, conditional only on the expressly stipulated source results and the elementary/classical facts proved or identified above.

For clarity, the C³ obstruction uses a scalar determinant nonvanishing on the entire zero section. The coordinate triples (z₁,z₂,w f_l) have determinant f_l, which need not be nonvanishing. Having three f_l with no COMMON zero does not contradict that scalar obstruction. No representing measure is treated as a Jensen measure.

## 7. Contribution boundary

The source owns all negative-curvature construction and the no-C³ conclusion, including the adjustable amplitude. Classical work owns normal infinite products, Cauchy–Schwarz, algebraic dependence, Baire selection and finite holomorphic generation. The proposed extra operation is the globally controlled scalar family extracted from the source's regularized logarithmic factors with a summable loss, then its use to separate all fibers by bounded functions. This author proof does not award a substantial-contribution gate; it may be judged a technical consequence of the explicit source structure. The full statement and proof must be reviewed as written, without replacing them with an easier local or infinite-dimensional assertion.
