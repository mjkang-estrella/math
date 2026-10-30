# Independent Structural232 correctness review, round 1

**Proposed verdict for parent adoption: PASS.** The submitted proof supports the entire unchanged frozen statement relative to the stipulated upstream truth. I found no essential repair, added hypothesis, narrowed quantifier, replacement theorem, or unresolved mathematical obligation. This includes the quantitative constants, all prescribed minimizing sides, and the smooth compatibility construction. This is a correctness proposal only; it assigns no contribution verdict or acceptance/count.

The objects reviewed are `selected/author/FROZEN-STATEMENT.md` (2057 bytes, SHA256 `9e57e9fcd07c3653bc8568c05f4e1ba57cf4ae56bd58f7b38a087b08ee7e1e68`) and `selected/author/AUTHOR-PROOF.md` (27938 bytes, SHA256 `477e211c486f14fd1118f0ceb2f1e550cb65303dc2eea1b65c357fb8437b78a7`) in the sole admitted author packet. I also read its other three author prose files, FINAL, outside REPORT, and private reading notes. Their auxiliary assertions are addressed below. Author originals were read-only; no correction has been inserted into them.

The review starts from the unchanged submission and the stipulated interfaces, not from any parent assessment or another review. All references to G and W below mean the two exact Source356 manuscripts at pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Their operative proofs are assumed true, including their strongest actual internal operations. I independently checked which operations the new argument uses and whether its modifications satisfy their interfaces. I did not treat the constant-curvature conclusion as an unrestricted variable-curvature index theorem.

## 1. Scope, signs, and exact ambient category

The frozen quantifiers are integer n≥3, finite p>n/3, v>0; a complete separable space with full support, m=H_d^n in precisely the source normalization, and unreduced RCD(0,n). The ball lower bound is for every center in the open B_2(o) and every radius in (0,1]. The defect is a single globally continuous function 0≤ρ≤1, tested against every pair of original global test vector fields and every nonnegative original global test function. The conclusion concerns every a,x,y in open B_1(o), perimeter≤1, every chosen minimizing constant-speed side, and every parameter, including degeneracies. Neither the proof nor this review changes these conditions.

G introduction, lines 24–82 (`eq:test-class`, `eq:test-vector-class`, `eq:curvature-definition`, `main:equivalence`), has exactly the frozen classes. D(Δ) is the L²-generator domain, Δ is nonpositive, and Test functions are bounded globally Lipschitz with Δf∈W^{1,2}. TestV consists of finite sums a∇b with both factors in that original Test class. In particular a bare gradient cannot globally be justified by inserting the constant 1 when m(X)=∞. The actual source remedy, `pre:bare-gradients`, uses a compact test cutoff equal to one near the gradient's support; the author uses that remedy.

The frozen curvature formula equals G's formula term for term. Integration by parts on a smooth space gives the convention ∇_U∇_V−∇_V∇_U−∇_[U,V], with positive round-sphere sectional evaluations R(U,V,V,U). The minus sign on the main curvature term in the differentiated-Hessian identity is consequently correct. The wedge quantity is |U|²|V|²−〈U,V〉², with no missing factor 2. It is nonnegative and integrable against bounded f and bounded ρ: it is at most ||U||_∞²|V|². Original curvature integrands are also globally integrable by the bounded-field/L²-derivative estimates in G preliminaries and forward lines 1230–1251. This is not a curvature hypothesis asserted only on charts.

Since ρ≤1, the frozen inequality implies the global sectional bound −1 on those same classes. Unreduced RCD(0,n) implies unreduced RCD(−(n−1),n) by monotonicity in the curvature parameter with the dimension and Cheeger energy fixed. G `main:equivalence` therefore gives global CBB(−1), in its exact n-dimensional Alexandrov category. Properness, geodesicity, local finite measure, and the noncollapsed tangent rank n are available from G preliminaries, lines 271–286; none is imported from an unstated smoothing assumption. The measure is never replaced or rescaled in this deduction. Complete global CBB(−1), not local CBB or CAT(−1), is the geometry used later.

## 2. Exact paid analytic interfaces and the variable modification

The operative source interfaces I read include the complete heat-index section, the complete frame section, G preliminaries, G's weak-Hessian comparison section, and the complete W calculus, drift, curvature-change, and every-geodesic proof sections. In particular:

- G `heat:regularity` gives local test regularity, uniform bounded velocities, and the fixed-viscosity terminal density/potential traces.
- `heat:density-laplacian` and `heat:weighted-estimates` give positive-time bounded densities, the integrable one-sided bound on cΔb, the weighted Hessian/Laplacian bounds, and small weighted products involving w.
- `heat:riccati-identity`, `heat:error-cancellation`, and `heat:viscous-index` are the differentiated identity, full cancellation, and terminal exhaustion, respectively.
- `heat:curve-compactness`, `heat:action-limit` (including `heat:strong-coefficient-velocity`), and `heat:common-paths` supply moment control, weighted strong convergence with fixed L² coefficients, and one common Borel prescription whose velocity is the actual path velocity.
- G `frames:path-calculus` and `frames:trial-density` give entire positive-time path frames and a countable family with endpoints fixed as global fields. The final `frames:hessian` proof gives the Radon extraction and countable-infimum mechanism.
- W `weight:every-geodesic` requires precisely bounded globally Lipschitz F, bounded continuous G, and the weak Hessian inequality for every compact original test gradient and nonnegative compact Lipschitz multiplier. It does not require F∈L² or an L² Hessian. Its drift-domain and variable-CD proof operations are paid at their full stated scope.

These are actual proof operations, rather than an inference from a catalogue or a source theorem title.

### Main curvature term and cancellation

Write η for the heat density to avoid confusion with the frozen defect ρ. At fixed viscosity, the source identity reads

    d/dt ∫η H_θ(Y,Y)
      = ∫η[2〈H_θY,D_cY〉−|H_θY|²]
        −R(Y,v_c,v_c,Y)(η)
        −H_{|w_c|²/2+cΔb_c}(Y,Y)(η).

The new hypothesis gives −R(Y,v_c,v_c,Y)(η)≤∫ηρ|Y∧v_c|². The fields and weight used here are genuine global tests after the source's cutoffs around the common compact trial support. Locality removes those cutoffs. Extension to compact Lipschitz weights uses `pre:tensor-continuity`: the additional right-hand side is a bounded fixed multiplier times an L¹-convergent wedge expression. It needs no derivative or Sobolev representative of ρ.

For the last Hessian term the author correctly retains the coarse κ=−1 cancellation. In the actual proof this error splits into a nonnegative |H_bY|² term, R(Y,w,w,Y), and two derivative terms. The inverse-viscosity products cancel before estimation. The residual factors are controlled by the weighted |w|⁴/c² estimate and vanishing weighted products with fixed L² coefficients. The Bochner part is split into a nonnegative measure plus an L² remainder; the quasi-continuous lower bound cΔb≥−e_c(t) controls its singular part, with ||e_c||_1→0 uniformly in the terminal exhaustion. The coarse curvature contribution R(Y,w,w,Y)≥−∫η|Y∧w|² vanishes by those same estimates. Thus using −1 there introduces no residual constant error and does not require multiplying a singular Bochner measure by the new ρ. This is an important distinction: the proof does not infer smallness of a differentiated acceleration error merely from w→0.

Completing the square gives 2〈H_θY,D_cY〉−|H_θY|²≤|D_cY|². With Y_ε=0, the initial pairing vanishes. For fixed c, the source first-order weak-Hessian formula and strong local terminal traces pass T↑1, giving precisely the author's (2.4). All limits in this step keep c, ε, the positive terminal datum, and the fixed global trial in the source order.

### Zero viscosity, prescribed paths, and terminal perturbation

For fixed bounded Y and bounded velocities, the difference between |Y∧v_c|² and |Y∧V|² has absolute value at most C|v_c−V|. Cauchy–Schwarz against η^c on the finite compact spacetime region and the source weighted strong convergence make its integral tend to zero. Multiplication by ρ≤1 preserves this estimate. The remaining fixed function ρ|Y∧V|² is in L¹, so weak-* density convergence passes that term. The derivative energy needs the stronger convergence with coefficient ∇Y, not just bounded Y; the submitted proof explicitly uses that source estimate. Its remaining fixed square is likewise in L¹. These arguments work for the fixed continuous ρ without regularizing it. Continuity is stronger than what these particular limits need; it is used later for the representative.

At the terminal Hessian, weak local W^{1,2} convergence of the potential pairs with fixed L² coefficients. The extra c∇log f tends uniformly to zero for the positive source class. The source's common-path proof identifies V with the actual pullback velocity by equality of actions, not only with a conditional average. It supplies the same prescription for every terminal weight. Accordingly f_λ=f_0+λ f_bar gives exactly π_{f_λ}=π_{f_0}+λπ_{f_bar}. The new energy is linear in the terminal plan, and its f_bar term is finite because of bounded speed, positive-time compression, bounded ρ, and compact trial derivatives. Sending λ↓0 yields (2.5) for every indicated compact Lipschitz f_0. There is no unsupported interchange of the c, terminal-time, and λ limits.

### Countable trials and Radon extraction

On a bounded terminal ball, use the source reference plan with a compact terminal cutoff equal to one on that ball. Each fixed global trial energy E_Y is locally integrable by its L² derivative bounds and positive-time compression. Taking one trial Y_t=(t−ε)Z/(1−ε), the functional E_0m−H_q(Z,Z) is positive on nonnegative compact Lipschitz weights. A dominating compact cutoff gives its sup-norm bound on every compact set. Density in C_c and Riesz representation produce a positive Radon measure ν. Hence

    H_q(Z,Z)=E_0m−ν=h_Zm+μ_s,   μ_s≤0.

The measure represents the fixed weak functional, so changing ε or the initial trial does not change it. Each other trial gives E_Ym−H_q≥0. Countability makes h_Z≤inf_Y E_Y valid on one conull set for that ε. The paid family fixes Y_ε=0 and Y_1=Z on the whole space, not merely at selected path endpoints.

Along a good radial path of speed r, parallel-transport the entire terminal vector Z(x) and put W_t=(t−ε)P(t)/(1−ε). The path calculus identifies its endpoint with Z(x), including zero-speed paths. Its derivative energy is |Z(x)|²/(1−ε). Its defect energy is bounded by

    r²|Z(x)|² ∫_ε^1 ((t−ε)/(1−ε))² ρ(γ_t) dt.

The variable energy is continuous in the source W^{1,2} path norm: derivative terms converge in L², and the wedge terms are bounded quadratic forms with coefficient norm at most r². Therefore the countable infimum is no larger than this energy, path by path. No measurable choice of approximating global trials is needed. A countable sequence ε↓0 and bounded convergence give h_Z≤(1+D_a)|Z|²; the nonpositive μ_s then gives the full measure inequality. Taking the full vector rather than a parallel/perpendicular decomposition only weakens the upper bound legitimately. In particular the source's more precise terminal radial-gradient trace is not an extra unstated prerequisite for this coarser trial.

This executes the variable-defect extension through all the paid operations. I find no generalized index lemma being assumed silently.

## 3. Radial potential, uniqueness, and the everywhere representative

For R>0 the radial datum u=min(2R d(a,·),2R²) is bounded, globally 2R-Lipschitz, and constant outside a compact set by properness. For r=d(a,x)<R and s=d(a,y)≤R,

    u(y)+d(x,y)²/2−r²/2 ≥ s(2R−r)+s²/2,

which is strictly positive unless y=a. For s≥R the initial value 2R² exceeds r²/2. Thus Q_1u=q_a on B_R(a), and a is the unique initial minimizer, including when x=a.

Q_1u is real-valued c-concave for c=d²/2, namely the c-transform of −u. Every minimizing a-to-x path for x∈B_R(a) is calibrated, and its reversal belongs to this prescribed potential's superdifferential. GRS Theorem 3.4, also explicitly used in G `heat:common-paths`, gives uniqueness of that whole geodesic for m-a.e. terminal x. This is stronger than uniqueness of one selected optimal plan and is what permits replacing the maximum by the prescribed path in the Lp estimate. A countable exhaustion in R suffices if a global conull set is desired; the proof only needs each fixed bounded ball.

For endpoints in a compact set, radial minimizers have uniformly bounded speed and remain in a compact ball. Arzelà–Ascoli and the closed minimizing-geodesic condition make their family compact. Uniformly convergent paths have convergent integrals of s²ρ(γ_s), since ρ is uniformly continuous on that compact ball. The maximum defining D_a therefore exists. Maximizers along a convergent endpoint sequence have a subsequential limiting minimizer to the limiting endpoint, proving upper semicontinuity of D_a. The elementary bound 0≤D_a≤r²/3 proves upper semicontinuity at a as well and justifies D_a(a)=0.

Thus D_a is an everywhere-defined Borel representative. It may be discontinuous at cut points; the proof does not assert otherwise. Its maximum dominates the prescribed path expression everywhere and equals it m-a.e. Only the latter assertion is used inside ambient measure norms and Hessian densities. No pathwise uniqueness is asserted at exceptional endpoints.

## 4. Exact GRS use, radial compression, and the Lp constant

I read GRS arXiv1305.4849v1, sections 2–3, including Proposition 3.1 and the complete proofs of Lemmas 3.2–3.3 and Theorem 3.4. Proposition 3.1 is the pointwise density inequality for the unique plan between absolutely continuous measures on RCD-star(K,N). Its proof localizes the integrated CD inequality to arbitrary Borel subsets of paths using uniqueness and nonbranching. Lemma 3.2 drops one term and passes to a singular endpoint by proper compactness. Theorem 3.4 gives prescribed-potential whole-geodesic uniqueness and then uniqueness for arbitrary terminal measures. These are the actual statements the author needs; an entropy bound by itself would not suffice.

Here the input is still unreduced RCD(0,n). It supplies the GRS interface at K=0, where the distortion coefficient is exactly t, for the same n and measure. I make no nonzero-K reduced/unreduced identification. The relevant inequality is

    η_t(γ_t)^(-1/n) ≥ (1−t)η_0(γ_0)^(-1/n)+tη_1(γ_1)^(-1/n).

Set V=m(B_2(a)); full support and local finiteness give 0<V<∞. Approximate δ_a by normalized sufficiently small open balls, with terminal probability V^(-1)m|B_2(a). These are bounded-support absolutely continuous probabilities. Dropping the initial term gives η_t≤t^(-n)/V for each t>0, uniformly in the approximation. The supports of the dynamical plans lie in a common compact family of bounded-speed geodesics. A weak subsequential limit has the desired endpoints; endpoint costs converge on this compact set, so it is optimal. For each fixed t, evaluation is continuous and testing against nonnegative continuous functions preserves the density domination. This proves the domination for every positive time as a measure inequality, without a common pointwise density version being required. Reversal and prescribed-potential uniqueness identify this limit with the radial Borel map almost everywhere. Multiplying by V yields

    (T_t)_#(m|B_2(a)) ≤ t^(-n)m.

No compression at t=0 is used. Conversely, if both endpoint densities are ≤Λ, retaining both terms gives η_t≤Λ for every t. These facts hold for open-ball restrictions regardless of the measures of their boundaries.

Since n≥3 and p>n/3, p>1. Minkowski is therefore applicable. Radial paths to B_2(a) stay in B_2(a), and r²≤4. The a.e. uniqueness already established gives

    ||D_a||_{Lp(B_2(a))}
      ≤4∫_0^1 t² ||ρ∘T_t||_p dt
      ≤4 ||ρ||_{Lp(B_2(a))} ∫_0^1 t^(2−n/p) dt
      =4 ||ρ||_{Lp(B_2(a))}/(3−n/p).

The integral converges exactly under the imposed strict inequality. The time-zero point can be omitted from the integral. Joint measurability follows from the Borel path prescription and evaluation. Finally a∈B_1(o) implies the strict inclusion B_2(a)⊂B_3(o). Thus the constant is exactly 4δ/(3−n/p), and δ is finite since ρ≤1 and B_3(o) has finite measure. This step does not use an unstated lower volume bound at centers outside the frozen region.

## 5. Flattening and the every-chosen-geodesic transfer

Choose the stated smooth nonincreasing θ with θ=1 on [0,1/2] and θ=0 on [2,∞). Such a smooth transition exists. The radial derivative of χ(r²/2) is rθ(r²/2), between 0 and 2; composition with distance gives the global 2-Lipschitz bound. F_a is bounded, equals q_a for d(a,·)≤1, and is constant for d(a,·)≥2. It need not be globally L², which W explicitly permits.

Dtilde=θ(q_a)D_a is nonnegative and upper semicontinuous. Where θ>0 this follows from the product with a continuous nonnegative factor. At θ=0, local boundedness D_a≤r²/3 forces the product to tend to zero from inside. In particular there is no support-boundary jump at radius 2. It vanishes outside the open B_2(a), is bounded by 4/3, and has global Lp norm at most 4δ/(3−n/p). Its closed support may meet the sphere of radius 2; no claim that the closed support lies in the open ball is needed, and its value on that sphere is exactly zero.

For the weak-Hessian formula, expand div(hθ(q_a)Z). The Sobolev chain rule for the locally Lipschitz q_a gives

    H_F(Z,Z)(h)
      = H_q(Z,Z)(hθ(q_a))
        + ∫hθ'(q_a)〈∇q_a,Z〉² dm.

This identity involves first derivatives, not a global W^{2,2} assertion for q_a. The first weight is compact Lipschitz; its support lies in the compact closed radius-2 ball, inside B_3(a), where the measure bound is available. The additional term is nonpositive. Multiplication of H_q by the continuous θ≥0 retains the nonpositive singular part. Since θ≤1, θ(1+D_a)≤1+Dtilde, giving exactly the required global weak inequality. Outside that region F is constant. Smooth flatness of θ at its constant region and the local weak calculation introduce no sphere or infinity boundary term. The wording about vanishing at the constant region does not require θ to become zero at a radius strictly smaller than 2.

For D_j(x)=sup_y(Dtilde(y)−j d(x,y)), each function is j-Lipschitz, between 0 and 4/3, and dominates Dtilde. The sequence decreases. For an approximately maximizing y_j with error tending to zero, nonnegativity of D_j and boundedness of Dtilde imply d(x,y_j)→0. Upper semicontinuity then gives limsup D_j(x)≤Dtilde(x). This proves convergence at every point, not just m-a.e.; attainment of the supremum is unnecessary.

Applying W to F_a and G_j=1+D_j is therefore exact. F is bounded globally Lipschitz; G_j is bounded continuous; the original full-support RCD(0,n) satisfies 1<n<∞; and the weak inequality holds for every required compact original gradient and compact nonnegative Lipschitz multiplier. I read the paid drift/resolvent and generator-domain closure, as well as the variable-CD and prescribed-path entropy proof, rather than treating an a.e. transport differentiation formula as an every-path theorem.

For each fixed chosen minimizing γ of length L, W gives (F∘γ)''≤L²(1+D_j∘γ). Integrating with the nonnegative Dirichlet Green kernel G(t,s)=min(t,s)−ts gives a lower bound for F above its endpoint chord minus L²t(1−t)/2 and minus the Green defect integral. The sign follows by subtracting the solution of that second-derivative equation: the remainder is concave. Continuity supplies endpoints. Because D_j decreases pointwise everywhere and is uniformly bounded, bounded convergence on this particular curve gives (3.5). This is the necessary justification for evaluating Dtilde along an ambient-null curve. The ambient Lp norm is not used until the subsequent averaging step.

## 6. Independent CBB(−1) endpoint-stability calculation

I independently re-derived the estimate using the actual directions of AKP Theorem 8.14, whose statement and proof I read in the admitted online-book extraction. In CBB(−1), a point on a side is at least as far from the opposite vertex as in the hyperbolic comparison triangle; a hinge with its actual angle has opposite side no longer than the model hinge; and two actual adjacent angles at an interior point of a minimizing side have sum at most π. These three statements, with these orientations, are sufficient. No CAT estimate enters.

Let A,x,y be in order with d(A,x)=h>0, d(x,y)=L, h+L≤1, and 0<h≤1/8. Let perturbed endpoints be within r≤1/8, and z=γ_t on any minimizing path joining them. Put l'=d(x',y'), T=tL, and b=d(x,z). Then |l'−L|≤2r, l'≤L+2r<2, and b≤r+t l'≤T+3r.

In the hyperbolic model the function cosh distance from A restricted to the comparison side solves C''=l'²C in the [0,1] parameter. Thus its endpoint interpolation has coefficients

    a_t(l)=sinh((1−t)l)/sinh l,   b_t(l)=sinh(tl)/sinh l,

with continuous values at l=0. For 0≤u≤1, the quotient is N(l)/D(l), where N=∫_0^u cosh(sl)ds and D=∫_0^1 cosh(sl)ds. On [0,2], D≥1, 0≤N≤D, and |N'|,|D'|≤sinh 2<4, hence |(N/D)'|≤8. Both coefficients lie in [0,1].

The two actual endpoint distances from A differ from h and h+L by at most r and are below 2. Their cosh errors are therefore at most 4r each. The two coefficient errors are at most 16r each; the baseline cosh values are below 4. Point-on-side comparison gives

    cosh d(A,z)
      ≥a_t(l')cosh d(A,x')+b_t(l')cosh d(A,y')
      ≥cosh(h+T)−136r
      ≥cosh(h+T)−200r.

The baseline identity is exact, because A,x,y are collinear in the model. No division by a potentially vanishing l' is made without its continuous extension.

For b,T>0 choose any minimizing [xz]. Let θ be its angle with the backward [xA] and α its angle with the forward [xy]. The latter two directions are opposite along the chosen minimizing segment. Adjacent-angle comparison gives α+θ≤π. Therefore cosα≥−cosθ. The actual θ is at least its hyperbolic comparison angle θbar in Axz, so cosθ≤cosθbar. The two hinge comparisons, with these inequalities in the stated order, give

    cosh d(z,w_t)
      ≤cosh b cosh T−sinh b sinh T cosα
      ≤cosh b cosh T+sinh b sinh T cosθ
      ≤[sinh(h+T)/sinh h]cosh b
        −[sinh T/sinh h]cosh d(A,z).

The last step substitutes the cosine rule
cosθbar=(cosh h cosh b−cosh d(A,z))/(sinh h sinh b).
This substitution is valid by continuous limits for a degenerate comparison triangle. If b=0 or T=0, the final displayed inequality is directly an equality, so no undefined angle is needed. L=0 is covered by T=0. Coinciding perturbed endpoints, endpoint parameters t=0,1, and z=A cause no additional denominator problem.

Let c_1=sinh(h+T)/sinh h and c_2=sinh T/sinh h. Both lie in [0,2/h], since h+T≤1, sinh1<2, and sinh h≥h. The exact identity

    c_1 cosh T−c_2 cosh(h+T)=1

cancels the baseline. As T+3r≤11/8 and sinh(11/8)<4, cosh b−cosh T≤12r, even if b<T. Consequently

    cosh d(z,w_t)−1 ≤(2/h)(12r)+(2/h)(200r)=424r/h.

Finally cosh s−1≥s²/2 gives d(z,w_t)²≤848r/h<900r/h, hence d(z,w_t)≤30√(r/h). The exponential bounds used above follow from their power series (for example e²<8 and cosh2<4); the quoted round constants are safely strict. This is uniform over every minimizing path satisfying the endpoint constraints, not just transport-selected paths. For r=0 the same continuous inequalities give uniqueness of the extendible segment, consistently with the source geometry.

## 7. Trimming, endpoint plans, and averaging constants

For the frozen triangle, write its chosen side in arclength as σ_s, 0≤s≤l. The two routes from a have lengths d(a,x)+s and d(a,y)+l−s. Their sum is the perimeter, so d(a,σ_s)≤1/2. Also l≤1/2 by the triangle inequality and perimeter bound. Thus F_a=q_a on the entire original side, including its endpoints. Moreover d(o,σ_s)<1+l≤3/2, so every endpoint-ball center used below lies strictly inside B_2(o).

Fix 0<h≤1/8 and r=h³/4096. In the long-side case l>4h, the trimmed endpoints σ_h and σ_{l−h} have separation L=l−2h>0 and admit the original backward extension A=σ_0 of length h. Their total extended length is l−h≤1. The radius is positive and at most 1/2097152, hence satisfies both the frozen volume range and the stability lemma's radius restriction.

Each endpoint ball has positive finite measure and at least v r^n. Its normalized restriction has density at most Λ=(v r^n)^−1. There exists a dynamical optimal plan between them, with bounded support and finite cost. The exact K=0 interpolation proved above bounds every intermediate marginal by Λ as well, including the endpoints. Every path in its support has endpoints in the closed radius-r balls and length at most L+2r; the endpoint measures themselves are concentrated on the open balls. The geometric estimate works with ≤r, so this distinction does not remove any relevant path.

For every such path and every t, stability and the global 2-Lipschitz bound give the pointwise error 60√(r/h) from F_a(γ_t) to q_a(σ_{h+tL}), and endpoint errors 2r each. The argument does not need F_a=q_a on perturbed paths or balls. This is why global flattening, rather than a local identity imposed on the transports, is sufficient.

With p'=p/(p−1), the marginal density satisfies

    ||η_s||_{p'}≤Λ^(1/p),

because ∫η_s=1 and ∫η_s^{p'}≤Λ^{p'−1}. Thus the expected defect at every time is at most 4δΛ^(1/p)/(3−n/p). One can integrate on path space directly: Dtilde is bounded Borel and evaluation is continuous, so Fubini applies. A joint choice of density versions is unnecessary; alternatively the spacetime marginal has a bounded Radon–Nikodym density. No value on an arbitrary null curve is controlled by Hölder at this stage; Hölder controls the absolutely continuous marginals of the average.

The Green kernel is nonnegative and has integral t(1−t)/2≤1/8. With length bound L+2r, the excess in the constant-curvature speed term is

    [(L+2r)²−L²]/8=(Lr+r²)/2≤r,

using L≤1 and r≤1. Endpoint errors combine with weights 1−t,t and cost 2r total, not 4r. The defect term is at most

    [(L+2r)²/8]·[4δ/(3−n/p)](v r^n)^(-1/p)
      ≤[5/((3−n/p)v^(1/p))]δ r^(-n/p),

because L+2r≤3 and 9/2≤5. These constants yield exactly (5.5). Although actual lengths are much smaller, the loose bounds preserve the claimed factor 5.

For r=h³/4096,

    60√(r/h)=60h/64=15h/16,
    3r/h=3h²/4096≤3/(64·4096)<1.

Hence 3r+60√(r/h)≤2h. Substituting r^(-n/p)=4096^(n/p)h^(-3n/p) produces exactly
B=5·4096^(n/p)/((3−n/p)v^(1/p)).
There is no extra factor of the terminal volume or a missing normalization. All uses of the lower ball-volume assumption have centers in B_2(o), radii in (0,1], and positive finite normalization. The defect integral is localized solely by the support of Dtilde and B_2(a)⊂B_3(o), not by requiring nearby paths to remain in that ball.

## 8. Endpoint restoration, parameter choice, and degeneracies

Put f(s)=q_a(σ_s)−s²/2. Since d(a,σ_s)≤1/2, the elementary difference-of-squares formula makes q_a∘σ 1/2-Lipschitz. Also s²/2 is l-Lipschitz with l≤1/2. The author's 2-Lipschitz estimate is consequently valid and deliberately loose. The chord c joining f(0),f(l) has slope of magnitude at most 2.

At each trimmed endpoint the difference f−c is bounded in absolute value by 4h, using the two Lipschitz bounds and the adjacent original endpoint. The difference between the trimmed chord and c is affine; its endpoint bounds therefore control the entire trimmed interval by 4h. Subtracting s²/2 converts the L²t(1−t)/2 term exactly into this chord comparison. The inner interval loses at most E+4h and the outer intervals at most 4h. If l≤4h, estimating from the closer endpoint instead gives f−c≥−4 min(s,l−s)≥−2l≥−8h. Thus the uniform displayed error 10h+Bδh^(-3n/p) is safe in both cases. The constant side has exact equality.

Let β=3n/p>0 and α=1/(1+β). For δ=0 the bound holds for every positive h≤1/8, so h↓0 gives zero error. For δ>0 set z=(Bδ)^α. If z≤1/8, taking h=z makes Bδh^(-β)=z and gives q-error≤11z. Multiplication by 2, and only then, gives the frozen squared-distance error 22z. This is a valid balancing choice; it need not be the exact stationary minimizer of 10h+Bδh^(-β), and the proof claims no sharper optimized constant.

If z>1/8 the possible squared-distance deficit is at most 1 (indeed the perimeter permits a better bound), whereas 22z>22/8>1. The large-defect case therefore needs no small-radius argument. At t=0,1 the comparison is immediate and consistent with the limiting argument. Cases a=x, a=y, collinear triples, multiple minimizing sides, and constant sides are all covered: every geometric and analytic step was applied to the original prescribed side, or to every nearby minimizer. Open balls and perimeter equality cause no limiting escape of the centers or of the defect localization.

## 9. Smooth S²×S² compatibility construction

I checked the complete compatibility calculation independently. It is a smooth example inside the frozen category, not a claim of a nonsmooth conformal-change theorem.

On the unit product S²×S², n=4, Ric_g=g, and sectional curvatures lie in [0,1], with mixed planes of curvature zero. A smooth nonnegative compactly supported Euclidean bump equal to |z|²/2 near zero is obtained by multiplying that quadratic by a smooth cutoff equal to one near zero and supported strictly inside the unit ball. In a fixed normal chart, u_ε=aε²φ(x/ε), extended by zero, is smooth: the support is contained in the chart and all derivatives match zero outside the scaled bump. With ε restricted to a fixed small range, the coordinate metric, inverse metric, and connection bounds give a single C≥1 for |u|≤Caε², |du|≤Caε, |Hess_g u|≤Ca, uniformly for 0<a≤1. Large higher derivatives as ε↓0 are not used.

Koszul's formula gives A_XY=du(X)Y+du(Y)X−g(X,Y)∇u for the connection difference. Substitution in R^u=R+d^∇A+A∧A, with the same curvature sign as above, yields for g-orthonormal X,Y

    K_{e^{2u}g}(X∧Y)
      =e^(-2u)[K_g(X,Y)−Hess u(X,X)−Hess u(Y,Y)
                +du(X)²+du(Y)²−|du|²].

Tracing using the transformed orthonormal frame e^(−u)E_i gives

    Ric_{e^{2u}g}=Ric_g−2(Hess u−du⊗du)
                         −(Δ_g u+2|du|²)g

in dimension 4, where Δ_g=tr Hess has nonpositive spectrum. There is no sign reversal from the use of a nonpositive generator. The negative quadratic-form perturbation is bounded by 6Ca+2C²a²ε_0²: the Hessian and trace contribute at most 2Ca+4Ca, and the negative gradient-square term at most 2C²a²ε_0². First reducing ε_0, then fixing one sufficiently small a>0, makes this at most 1/2 for every ε, hence Ric_{g_ε}≥g/2>0. The analogous sectional lower bound is at least −e^(2Caε_0²)(2Ca+C²a²ε_0²); the same a can be reduced to make it ≥−1 uniformly.

At b, u=0, du=0, and Hess_g u=a g. The mixed sectional curvature is therefore exactly −2a, independently of ε. This establishes that the free parameter is not forced to vanish by Ricci nonnegativity. The minimum sectional curvature is continuous in x: in local orthonormal trivializations it is the minimum of a continuous function on the compact Grassmannian. Thus ρ_ε=max(0,−min K) is globally continuous, lies in [0,1], vanishes outside the coordinate ε-ball, and is bounded by a constant times a. Its support has uniformly O(ε⁴) Hausdorff measure, so ||ρ_ε||_Lp≤C_p a ε^(4/p)→0 for every fixed finite positive p, in particular every allowed p>4/3.

Use m_ε=H^4_{d_{g_ε}} itself. On a smooth manifold this equals Riemannian volume with the source's fixed Hausdorff convention; if that convention carries a dimensional constant, the same constant applies to g and every g_ε. Consequently dm_ε=e^{4u}dm_g exactly. The proof does not select a new normalization to obtain its bound. Smooth Ricci≥0 gives unreduced RCD(0,4) for this measure. Constant multiplication inherent in a fixed Hausdorff convention does not alter that curvature-dimension condition. Compactness gives completeness and finite measures, and the length metric has full support and dimension/tangent rank 4.

The smooth curvature inequality extends to all original global test fields and weights, not just smooth ones. The author's stated closure is justified by the already cited source calculus: on this fixed compact smooth manifold, heat approximation of the finitely many test functions is smooth, uniformly bounded with uniformly bounded gradients, and converges in the graph/Sobolev norms giving strong L² Hessians, covariant derivatives, and divergences. Nonnegative test weights can be approximated nonnegatively, uniformly and strongly in W^{1,2}. The source tensor-continuity calculation then passes the smooth integration-by-parts identity; the bounded continuous ρ_ε wedge term passes in L¹. Compactness removes any infinity boundary issue. This spells out the approximation asserted in the submission; it is not an additional smoothness hypothesis on its Test class.

Finally, L=e^{Caε_0²} uniformly compares lengths and volume measures. The displayed inclusions and m_ε≥L^(−4)m_g give

    m_ε(B_r^{g_ε}(x))≥L^(−4)m_g(B_{r/L}^g(x))
                       ≥c_0 L^(−8)r⁴,   0<r≤1,

where c_0=inf_{x,0<s≤1}m_g(B_s(x))/s⁴>0. Uniform normal charts handle small s; for larger s, monotonicity from one small radius and compactness give a positive lower bound. Thus one fixed v=c_0L^(−8)>0 works for all centers, hence in the frozen local range. The compatibility family satisfies every joint hypothesis in dimension 4, with negative sectional curvature and defect norm tending to zero. No example for every n, sharpness of α, or metric-limit assertion is claimed.

## 10. Objections considered, resolutions, and limits of this verdict

The following were substantive candidate objections rather than assumptions of correctness.

1. **A source constant-curvature Hessian bound does not imply a variable-defect formula.** Resolved by the actual heat-identity calculation and each subsequent limit in §2 above. Bounded ρ enters only the main absolutely continuous curvature-energy integrand; the entire paid cancellation is retained.
2. **Weak convergence cannot pass a quadratic velocity energy.** Resolved by `heat:strong-coefficient-velocity`, with ∇Y for the derivative energy, and by the explicit bounded-wedge estimate for the new term. Weak-* density convergence is used only on the remaining fixed L¹ integrands.
3. **A trial approximating a vector on one curve might violate global endpoint identities or require an unavailable measurable selection.** Resolved by the source's countable globally endpoint-fixed family, positivity of each Radon comparison, and a pathwise infimum. The author expressly makes no simultaneous measurable-trial claim.
4. **Optimal-plan uniqueness alone would not remove other radial minimizers from the maximum.** Resolved by prescribed-potential whole-geodesic uniqueness in GRS Theorem 3.4, applied to the actual real-valued Hopf–Lax potential. All a-to-x minimizers are calibrated there.
5. **An Lp function cannot be controlled on every ambient-null curve.** Resolved by the maximum-defined upper-semicontinuous representative, everywhere-decreasing Lipschitz majorants, the exact W hypotheses, and bounded convergence on each chosen curve before averaging.
6. **Flattening could create a positive sphere singularity or omit a chain-rule term.** Resolved by the first-order weak chain formula, θ'≤0, multiplication of the nonpositive singular Hessian part by θ≥0, and the globally constant continuation. The closed-support/open-ball wording is harmless because Dtilde is zero at radius 2.
7. **The density estimate might use reduced curvature with a different nonzero curvature or a different dimension.** Resolved by using GRS only at K=0 and N=n; both distortion normalizations are t. The original unreduced hypotheses are kept.
8. **Endpoint stability might reverse a CAT/CBB inequality or fail for nonselected paths.** Resolved by the independently checked three AKP directions and the explicit hyperbolic cancellation. The lemma quantifies over all minimizing endpoint-perturbed paths, including degeneracies, and uses the original backward extension.
9. **The rate could lose a volume, a factor 2, or endpoint error.** Resolved by the normalized density Λ, the Green integral 1/8, combined endpoint cost 2r, speed cost r, defect factor at most 9/2≤5, radius substitution, and the final squared-distance multiplication. The displayed 10 and 22 are valid upper bounds; exact stationary minimization is unnecessary.
10. **The smooth family could violate Ricci, exact measure, completeness, or uniform noncollapse.** Resolved by the uniform choices and the calculations in §9. The compact smooth approximation of global tests is the closure explicitly invoked in the submission, not a substitution of test classes.

The clarifications in these resolutions are consequences of the text's stated inequalities and its expressly invoked paid operations. They do not change a hypothesis, a constant, a test class, a theorem quantifier, or a proof strategy. In particular, I have not certified a repaired weaker result. The original statement and proof remain the objects of the proposed PASS.

The strongest simpler alternatives were also considered for correctness purposes. Coarse CBB(−1) alone provides no small-δ conclusion. Direct integration of a merely ambient-a.e. Hessian density on a chosen side is invalid. An entropy-only density estimate is insufficient for the radial Lp calculation, and qualitative nonbranching/compactness supplies no explicit endpoint-stability constant. None is used as a replacement in this proof. Conversely, no new noncollapsed frame theorem, weighted-generator regularity theorem, or every-geodesic upgrade is demanded: those precise mechanisms are already stipulated and have compatible hypotheses here.

No unresolved analytic or selection premise remains for the new deductions under the stated upstream stipulation. My independent primary reading was scoped to the operative Gigli distributional definition/symmetry proof, GRS density and uniqueness arguments, and AKP 8.14 comparison proof; it was not a recursive audit of all cited antecedents. The complete actual source analytic mechanisms were read and paid, not re-proved against their primary dependencies. Other primary-reading and formal statements in the submission remain limited exactly as disclosed in the separate reading/access report. The Lean theorem I inspected ends in `sorry`, so no formal proof support is assigned. There is no claim here about literature priority, excluded history, GH stability, measurable defects, collapsed or weighted variants, noncomplete spaces, or sharpness.
