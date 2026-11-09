# Author proof of the unchanged frozen statement r232-Q

This is a discovery author-proof submission, not an independent correctness or contribution verdict. The statement is exactly FROZEN-STATEMENT.md, SHA256 9e57e9fcd07c3653bc8568c05f4e1ba57cf4ae56bd58f7b38a087b08ee7e1e68. All upstream proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. No source conclusion is being nominated as new. The proof uses the original global test classes in that statement throughout.

## 1. Paid interfaces and the coarse geometry

Write G for the canonical characterization paper and W for the every-geodesic companion. Their drivers, operative includes, comparisons, applications, figure source and bibliographies were read before freezing. Exact authentication and reading records are separate. Labels below refer to those exact files at the pin.

G, main:equivalence, applied with κ=−1, gives CBB(−1). Indeed unreduced RCD(0,n) implies unreduced RCD(−(n−1),n) by monotonicity of the same CD coefficients; quadratic Cheeger energy is unchanged. Since 0≤ρ≤1, the frozen global sectional inequality implies R(U,V,V,U)(f)≥−∫f|U∧V|² for every original global admissible triple. Full support and m=H_d^n are hypotheses, not inferred from the tensor. Thus all hypotheses of G are present. In particular X is a proper n-dimensional Alexandrov length space; the source's noncollapsed frame calculus has tangent rank n. There has been no rescaling or change of reference measure.

The following established operations are paid: G's global test-calculus approximation and compact localization (pre:approximation, pre:bare-gradients, pre:tensor-continuity); its heat construction, differentiated-Hessian identity, acceleration-error cancellation, strong weighted velocity convergence, common prescribed-potential paths and terminal trace (heat:riccati-identity, heat:error-cancellation, heat:strong-coefficient-velocity, heat:common-paths); its all-time frame calculus and countable trial density (frames:path-calculus, frames:trial-density); the countable-infimum measure extraction in frames:hessian; and W's entire weak-Hessian-to-every-minimizer theorem, including its drift and variable-CD arguments. We use these operations rather than claiming they are additions here.

We also use optimal transport uniqueness and pointwise density interpolation on finite-dimensional RCD spaces. For clarity, the two special estimates needed below are proved in §3 from their standard density inequality. The actual primary proof of that inequality was read in Gigli–Rajala–Sturm (GRS), arXiv1305.4849v1, Proposition3.1; their Lemma3.2 and Theorem3.4 prove the singular-endpoint approximation and prescribed-potential uniqueness used here. GRS is written for RCD-star. Our hypothesis remains unreduced RCD(0,n), which implies that interface; at K=0 its distortion coefficients are exactly t. No nonzero-curvature replacement of an unreduced dimensional condition is made.

The operative Alexandrov input is point-on-side and hinge comparison, including the adjacent-angle inequality, in Alexander–Kapovitch–Petrunin (AKP), Theorem8.14 and its proof. Only κ=−1 is used; there is no positive-curvature perimeter issue in that application. The perimeter≤1 in our theorem fixes the explicit constants and the region on which squared distance agrees with its flattened version.

## 2. Retaining the variable defect in the source index construction

We first prove the following auxiliary inequality. Fix a∈X, put q_a(x)=d(a,x)²/2, and define

 D_a(x)=d(a,x)² max_{γ∈Geo(a,x)} ∫_0^1 s²ρ(γ_s) ds.                                      (2.1)

All geodesics here have constant speed and run from a to x. At x=a set D_a(a)=0. For each compact test gradient Z, on every bounded ball about a the weak Hessian H_{q_a}(Z,Z) is a signed Radon measure and

 H_{q_a}(Z,Z)≤(1+D_a)|Z|²m.                                                              (2.2)

The singular part of this measure is nonpositive. This is a variable-coefficient modification of the supplied index proof, not an invocation of its constant-curvature conclusion with a point-dependent parameter.

Here are the modifications in full. Use G's heat construction with the coarse constant κ=−1 in every regularity, density, tail and acceleration-error estimate. Denote its viscous density by η_t^c, to distinguish it from the defect ρ. On a fixed positive-time interval [ε,1], for any admissible compactly supported global trial Y with Y_ε=0 and Y_1=Z, the exact source Riccati identity is

 d/dt ∫η^c H_{θ^c}(Y,Y)
 =∫η^c[2H_{θ^c}(D_cY,Y)−|H_{θ^c}Y|²]
   −R(Y,v_c,v_c,Y)(η^c)−H_{|w_c|²/2+cΔb_c}(Y,Y)(η^c),
 D_cY=∂_tY+∇_{v_c}Y.                                                                    (2.3)

As in the source, local heat gradients and the density in this formula are multiplied by global test cutoffs that are identically one on a neighborhood of the common compact support of the trial. Locality and tensoriality remove the cutoffs from (2.3). Thus the frozen global tensor assumption is being applied to actual global test fields and nonnegative test multipliers. Where the source admits compact Lipschitz multipliers by approximation, the same approximation remains valid: the new right side contains the fixed bounded multiplier ρ, so convergence of f_j|Y_j∧v_j|² in L¹ also gives convergence after multiplication by ρ. There is no derivative of ρ in this operation, no dense-family-only curvature assumption, and no cutoff at infinity left in the resulting local identity.

Use the variable bound in the main curvature term:

 −R(Y,v_c,v_c,Y)(η^c)≤∫η^c ρ |Y∧v_c|².

The last term of (2.3) is treated by G's full acceleration-error cancellation using the already available coarse bound −1. Its integrated negative contribution is at most ε_c→0, with c→0 and the trial and ε fixed. Completing the square in the first term and taking the source terminal trace therefore gives

 H_{φ_1^c+c log f}(Z,Z)(f)
 ≤∫_ε^1∫η_t^c[|D_cY|²+ρ|Y∧v_c|²] dm dt+ε_c.                                          (2.4)

This step does not claim that small velocity error by itself controls a differentiated error: the source cancellation is retained in full.

The source proves strong convergence with fixed L² tensor coefficients and uniform bounds for the densities and velocities on this support. Consequently the curvature-defect term passes to the limit. More explicitly, the difference of its quadratic velocity expressions is bounded in absolute integral by a constant times the weighted L² difference of velocities, since ρ and Y are bounded. For the remaining fixed limiting integrand, weak-* convergence of η_t^c applies to the compactly supported L¹ function ρ|Y∧V|². The covariant-derivative energy passes by the source's stronger coefficient convergence with coefficient ∇Y. The first-order formula for the terminal Hessian gives the terminal convergence. Finally the positive terminal regularization f+λf_bar is removed by the common prescribed-potential path map and linearity in terminal density, exactly as in G. Thus for every nonnegative compact Lipschitz terminal f,

 H_{Q_1u}(Z,Z)(f)
 ≤∫ f(x) ∫_ε^1 [|D_tY(γ^x_t)|²+ρ(γ^x_t)|Y(γ^x_t)∧v_t|²] dt dm(x).                     (2.5)

These paths are the same terminal-a.e. prescription for all f. They have bounded speed and bounded compression on [ε,1]. The velocity is the actual pullback velocity, not a conditional average. Those facts, including the global density tails used in constructing the plan, are part of the paid source operation.

Take G's radial initial datum u=min{2R d(a,·),2R²}. On B_R(a), Q_1u=q_a and every calibrated path starts at a. For completeness, if r=d(a,x)<R and s=d(a,y), then for s≤R,
 2Rs+d(x,y)²/2−r²/2≥2Rs+(r−s)²/2−r²/2=s(2R−r)+s²/2≥0,
with equality only s=0; if s≥R the initial cost 2R² already exceeds r²/2. The same argument covers the truncation region. Hence the initial minimizer is a. The source prescribed-potential uniqueness gives a unique such whole geodesic for m-a.e. terminal x.

Fix Z and ε. For one global trial, its right-hand energy E_0(x) in (2.5) is locally integrable by positive-time compression and the trial's L² derivative bounds. The functional E_0m−H_{q_a}(Z,Z) is positive on nonnegative compact Lipschitz functions. Testing against a cutoff equal to one on a given compact set bounds it in the uniform norm there; extension to C_c and Riesz representation yield a positive Radon measure ν. Thus H_{q_a}(Z,Z)=E_0m−ν, with nonpositive singular part. This repeats the exact paid measure-extraction operation and shows why no pointwise curvature representative is needed.

Use the source's countable trial family with the prescribed GLOBAL endpoints 0 and Z. On a common full-measure set the absolutely continuous density h_Z of this measure is bounded above by every trial energy, hence by their countable infimum. On each such radial path parallel transport the full terminal vector Z(x) to P(t), and choose the pathwise field

 W_t=((t−ε)/(1−ε))P(t).

Its covariant derivative has squared norm |Z(x)|²/(1−ε)² and |W_t∧v_t|²≤((t−ε)/(1−ε))² |Z(x)|²r², because |v_t|=r. The paid pathwise trial density approximates W with its endpoints fixed; the variable energy is continuous in that pathwise norm since ρ≤1 and the speed is bounded. Therefore

 h_Z(x)≤|Z(x)|²/(1−ε)
  +r²|Z(x)|² ∫_ε^1 ((t−ε)/(1−ε))²ρ(γ^x_t)dt.                                          (2.6)

No measurable family of approximating global trials is asserted or needed: the infimum is countable, and the approximation is used path by path. Along a countable sequence ε↓0, bounded convergence gives (2.2), first almost everywhere for the density and then as a measure including the already nonpositive singular part. The maximum in (2.1) is an upper bound on the chosen path value everywhere, and equals it almost everywhere by the uniqueness just proved. The radius R was arbitrary since the coarse curvature is negative. This completes the auxiliary inequality.

## 3. Radial compression, Lp control, and a representative defined on every path

The set of geodesics from a to points in a fixed compact set is compact in the uniform topology: their speeds and images are bounded and X is proper. Since ρ is continuous, the integral in (2.1) is continuous under uniform convergence of those paths. Maximizers exist, and selecting maximizing paths along x_j→x and taking a subsequence shows limsup D_a(x_j)≤D_a(x). Thus D_a is upper semicontinuous. Also 0≤D_a(x)≤d(a,x)²/3. This specifies the representative even at cut points and is essential for the every-path step.

Let T_t(x) be the point at time t on the unique a-to-x radial minimizer, for almost every x in B_2(a). Then

 (T_t)_#(m|B_2(a))≤t^(−n)m,  0<t≤1.                                                     (3.1)

To justify the constant, put V=m(B_2(a)) and normalize the terminal measure to V^(−1)m|B_2(a). Approximate the initial point mass at a by normalized small balls. For each resulting optimal plan the pointwise CD(0,n) inequality is

 η_t(γ_t)^(−1/n)≥(1−t)η_0(γ_0)^(−1/n)+tη_1(γ_1)^(−1/n).

Dropping its first nonnegative term gives η_t≤t^(−n)/V. All supports and speeds are uniformly bounded. Compactness of the plans and lower semicontinuity of integration against continuous nonnegative tests preserve this density bound in the limit to the point mass. Optimality also passes; reversing the limiting plan and using prescribed-potential uniqueness identifies its paths with T_t for almost every terminal point. Multiplying by V proves (3.1). There is no bounded-compression assertion at the singular time t=0.

A second consequence, used later, is that the unique optimal plan between two bounded-support probability densities bounded by L has all time marginals bounded by L. Indeed both terms on the right of the same inequality give η_t^(−1/n)≥[(1−t)+t]L^(−1/n). The pointwise inequality follows from the CD inequality by restriction to arbitrary Borel sets of paths and uniqueness/nonbranching, exactly as in GRS Proposition3.1; it is stronger than an unsupported entropy-only bound.

Now p>n/3 and n≥3 imply p>1. Minkowski's integral inequality, (3.1), the bound r²≤4, and the fact that all radial points remain in B_2(a) give

 ||D_a||_{Lp(B_2(a))}
 ≤4∫_0^1 t² ||ρ∘T_t||_{Lp(B_2(a))}dt
 ≤4∫_0^1 t^(2−n/p)dt ||ρ||_{Lp(B_2(a))}
 =4/(3−n/p) ||ρ||_{Lp(B_2(a))}.                                                         (3.2)

The maximum over radial geodesics in D_a may be replaced by T_t inside this Lp calculation because all radial minimizers are unique for almost every terminal x. This is not a claim of uniqueness at every point. For a∈B_1(o), B_2(a)⊂B_3(o), so the final norm in (3.2) is at most δ.

Choose a smooth nonincreasing θ:[0,∞)→[0,1] with θ=1 on [0,1/2] and θ=0 on [2,∞). Put χ(q)=∫_0^q θ(s)ds and

 F_a=χ(q_a),   D̃_a=θ(q_a)D_a.

Then F_a is bounded and globally 2-Lipschitz, equals q_a on B_1(a), and is constant outside B_2(a). To see the Lipschitz constant without any smooth structure, its radial profile has derivative θ(r²/2)r≤2. The global bound follows by composition with the 1-Lipschitz distance function. The function D̃_a is nonnegative, upper semicontinuous, vanishes outside B_2(a), is bounded by 4/3, and satisfies

 ||D̃_a||_{Lp(X)}≤4δ/(3−n/p).                                                           (3.3)

For a compact global test gradient Z and a nonnegative compact Lipschitz multiplier h, the first-order weak-Hessian formula gives the chain rule

 H_{F_a}(Z,Z)(h)=H_{q_a}(Z,Z)(hθ(q_a))
                   +∫hθ'(q_a)〈∇q_a,Z〉²dm.

All nonzero terms are supported in the compact closure of B_2(a), inside the ball B_3(a) where (2.2) is available. In particular hθ(q_a) is an admissible compact Lipschitz weight for that measure. The formula follows by expanding div(hθ(q_a)Z); it needs no assertion that q_a is globally in W^{2,2}. Since θ'≤0, multiplication by θ preserves the sign of the singular part, and θ≤1, we obtain

 H_{F_a}(Z,Z)(h)≤∫h(1+D̃_a)|Z|²dm.                                                       (3.4)

There are no boundary terms at radius2 or at infinity: θ and the radial gradient vanish smoothly before the constant region, and the weak calculation is inside B_3(a). No change of measure is used.

For integers j≥1 define

 D_j(x)=sup_{y∈X}(D̃_a(y)−j d(x,y)).

These functions are globally j-Lipschitz, satisfy 0≤D̃_a≤D_j≤4/3, and decrease to D̃_a at every point. Indeed a nearly maximizing y_j has d(x,y_j)≤(4/3+1)/j, because D_j(x)≥D̃_a(x)≥0. Upper semicontinuity then gives limsup D_j(x)≤D̃_a(x). This verifies convergence of the specified representative, not only convergence almost everywhere.

Apply the full companion W to the bounded globally Lipschitz function F_a and the bounded continuous Hessian upper bound 1+D_j on the full-support RCD(0,n) space, with 1<n<∞. It yields, along EVERY constant-speed minimizing γ:[0,1]→X of length L,

 (F_a∘γ)''≤L²(1+D_j∘γ)

in one-dimensional distributions. Let G(t,s)=min{t,s}−ts be the nonnegative Dirichlet Green kernel for −d²/dt² on [0,1]. Integrating the inequality with its endpoint values gives

 F_a(γ_t)≥(1−t)F_a(γ_0)+tF_a(γ_1)−L²t(1−t)/2
                         −L²∫_0^1 G(t,s)D_j(γ_s)ds.

One can derive this directly by subtracting the solution with that second derivative and zero endpoint data; the remaining distributionally concave continuous function lies above its endpoint chord. Bounded convergence, now on this particular chosen path, gives

 F_a(γ_t)≥(1−t)F_a(γ_0)+tF_a(γ_1)−L²t(1−t)/2
                         −L²∫_0^1 G(t,s)D̃_a(γ_s)ds.                                    (3.5)

No integral estimate for the trace of an arbitrary Lp representative on γ has been used. We will bound an average of the last term by transport compression, and then quantitatively compare the averaged paths with the specified side.

## 4. An explicit estimate for endpoint perturbations of an extendible side

We need a quantitative substitute for qualitative uniqueness/compactness of nearby paths. In any CBB(−1) space, let A,x,y lie in this order on a minimizing segment, with

 d(A,x)=h,  d(x,y)=L,  0<h≤1/8,  h+L≤1.

Suppose d(x',x),d(y',y)≤r≤1/8, and let γ be ANY minimizing constant-speed path from x' to y'. If w_t is the point at distance tL from x on the chosen segment [xy], then

 d(γ_t,w_t)≤30 sqrt(r/h),  0≤t≤1.                                                        (4.1)

Here is an explicit proof, valid also near cut loci. Write l'=d(x',y'), z=γ_t and T=tL. Then |l'−L|≤2r and l'≤2. Put

 a_t(l)=sinh((1−t)l)/sinh l,  b_t(l)=sinh(tl)/sinh l,

using the continuous values 1−t,t at l=0. Both coefficients belong to [0,1]. For 0≤u≤1,

 sinh(ul)/sinh l = [∫_0^u cosh(sl)ds]/[∫_0^1 cosh(sl)ds].

On 0≤l≤2 the denominator is at least1, the numerator is at most the denominator, and the absolute derivatives of each integral are at most sinh2<4. The quotient rule therefore gives |a_t'(l)|,|b_t'(l)|≤8, uniformly in t, including the continuous endpoint at l=0.

Hyperbolic point-on-side comparison gives

 cosh d(A,z)≥a_t(l')cosh d(A,x')+b_t(l')cosh d(A,y').

The endpoint distances differ from h and h+L by at most r and are less than2. Thus their cosh values differ by at most4r. The two coefficient differences are at most16r each; the baseline cosh values are less than4. The total error from replacing l',x',y' by L,x,y is therefore at most

 2·4r+2·16r·4=136r≤200r.

The degenerate baseline segment satisfies the exact hyperbolic identity
 a_t(L)cosh h+b_t(L)cosh(h+L)=cosh(h+T).
It follows that

 cosh d(A,z)≥cosh(h+T)−200r.                                                             (4.2)

Next put b=d(x,z). The triangle inequality gives b≤r+t l'≤T+3r. At x, the directions to A and toward y are opposite. If b>0 and T>0, let θ be the actual angle between [xA] and a chosen [xz], and α the actual angle between that [xz] and the forward [xy]. The adjacent-angle inequality in AKP8.14 gives α+θ≤π. Hinge comparison gives θ at least the hyperbolic comparison angle of Axz and

 cosh d(z,w_t)≤cosh b cosh T−sinh b sinh T cosα
              ≤cosh b cosh T+sinh b sinh T cosθ
              ≤[sinh(h+T)/sinh h]cosh b−[sinh T/sinh h]cosh d(A,z).                       (4.3)

The last line is just the hyperbolic cosine rule for the comparison angle at x in Axz. If b=0, (4.3) is an equality by the hyperbolic addition identity; if T=0 it is also an equality. Thus no undefined zero-length angle is used. If L=0, T=0 covers every t. Degenerate comparison triangles may equivalently be treated by the continuous coefficient formulas above.

Let c_1=sinh(h+T)/sinh h and c_2=sinh T/sinh h. Both are nonnegative and at most2/h, since h+T≤1, sinh1<2 and sinh h≥h. Also

 c_1 cosh T−c_2 cosh(h+T)=1.

Using b≤T+3r and sinh(T+3r)≤sinh(11/8)<4, the mean value theorem gives cosh b−cosh T≤12r. Inserting (4.2) into (4.3) therefore yields

 cosh d(z,w_t)−1≤(2/h)12r+(2/h)200r=424r/h.

Since cosh s−1≥s²/2 for s≥0, d(z,w_t)²≤848r/h<900r/h, proving (4.1). This estimate uses the extension of [xy] backward by h; it does not assert uniform Lipschitz dependence of geodesics on arbitrary endpoints.

## 5. Transport averaging around a prescribed trimmed side

Fix any triangle and any chosen side σ covered by the frozen statement, and reparametrize σ by arclength s∈[0,l], l=d(x,y). Every point of σ has distance at most half the triangle perimeter from a: the two routes through x and y have lengths d(a,x)+s and d(a,y)+l−s, whose sum is the perimeter. Hence

 d(a,σ_s)≤1/2.                                                                          (5.1)

In particular F_a(σ_s)=q_a(σ_s). Also σ⊂B_2(o), since d(o,x)<1 and l≤1/2; all endpoint-ball centers below satisfy the assumed noncollapse condition.

Fix 0<h≤1/8 and set r=h³/4096. First suppose l>4h. Let

 x_0=σ_h, y_0=σ_(l−h), L=l−2h.

Let μ_0 and μ_1 be the normalized restrictions of m to B_r(x_0) and B_r(y_0). Their densities are at most Λ=(v r^n)^(−1), by the frozen lower ball-volume bound. They have bounded support, so their optimal dynamical plan π exists and, by §3, all time marginals have densities η_s≤Λ. Its individual path lengths l_γ are at most L+2r.

Take A=σ_0 in §4. The segment from A through x_0 to y_0 has backward extension h and total length h+L=l−h≤1. For every path in π, its endpoints belong to the indicated balls; (4.1) applies to that individual path. Consequently, with w_t=σ_(h+tL),

 |F_a(γ_t)−q_a(w_t)|≤60 sqrt(r/h),
 |F_a(γ_0)−q_a(x_0)|≤2r,  |F_a(γ_1)−q_a(y_0)|≤2r.                                      (5.2)

These inequalities use the global 2-Lipschitz bound for F_a. It is unnecessary to assert that F_a=q_a on the supports of μ_i or on the nearby paths.

For every s, Hölder's inequality and ∫η_s dm=1 give

 ∫D̃_a(γ_s)dπ(γ)=∫D̃_a η_s dm
 ≤||D̃_a||_p ||η_s||_(p/(p−1))
 ≤||D̃_a||_p Λ^(1/p)
 ≤[4/(3−n/p)] δ (v r^n)^(−1/p).                                                        (5.3)

Thus null sets carrying exceptional curves cannot create an uncontrolled averaged term. Formula (3.5) is valid on every curve before averaging, and (5.3) uses full marginal absolute continuity at each time; these are different operations.

Integrate (3.5) against π, using (5.2), (5.3), ∫_0^1G(t,s)ds=t(1−t)/2≤1/8, and l_γ≤L+2r. The part of the speed term in excess of L²t(1−t)/2 is at most

 [(L+2r)²−L²]/8=(Lr+r²)/2≤r,

because L≤1 and r≤1. The two endpoint averages together cost at most2r, not4r, since their convex weights sum to one. The curvature-defect term is at most

 [(L+2r)²/8]·[4/(3−n/p)]δ(v r^n)^(−1/p)
 ≤[5/((3−n/p)v^(1/p))]δ r^(−n/p),                                                       (5.4)

where (L+2r)≤3 suffices for the constant 5 (9/2≤5). Therefore, uniformly for t∈[0,1],

 q_a(w_t)≥(1−t)q_a(x_0)+tq_a(y_0)−L²t(1−t)/2−E,
 E=3r+60sqrt(r/h)+[5/((3−n/p)v^(1/p))]δr^(−n/p).                                        (5.5)

With r=h³/4096, the middle term is 15h/16 and 3r≤h. In particular

 E≤2h+Bδh^(−3n/p),
 B=5·4096^(n/p)/((3−n/p)v^(1/p)).                                                       (5.6)

All constants are independent of the particular triangle, side, t, or the endpoint-ball transport. The localization of the defect norm used only B_2(a)⊂B_3(o); no uncontrolled integral outside the stated region enters (5.3).

## 6. Restoring the endpoints and optimizing the radius

Let f(s)=q_a(σ_s)−s²/2 on [0,l]. From (5.1), q_a∘σ is 1/2-Lipschitz, while s²/2 is l-Lipschitz with l≤1/2. In particular f is 2-Lipschitz, a deliberately loose bound. The elementary identity

 (1−t)h²+t(h+L)²−(h+tL)²=t(1−t)L²

shows that (5.5) is exactly the assertion that f lies above the chord joining f(h),f(l−h), up to error E, on the trimmed interval.

Let c(s) be the chord joining f(0),f(l). Its slope has absolute value at most2. At s=h and s=l−h, |f(s)−c(s)|≤4h by the two Lipschitz bounds. The difference of the two affine chords is affine, so throughout the trimmed interval their difference is at most4h. Thus f(s)≥c(s)−E−4h there. On the two outer intervals the same Lipschitz bounds give f(s)≥c(s)−4h directly. If instead l≤4h, the direct Lipschitz estimate gives f(s)≥c(s)−2l≥c(s)−8h on the entire side. The constant side l=0 has exact equality.

Combining both cases with (5.6), and enlarging only a numerical constant, gives for every 0<h≤1/8 and every s=tl,

 q_a(σ_t)≥(1−t)q_a(x)+tq_a(y)−t(1−t)l²/2
                           −10h−Bδh^(−3n/p).                                          (6.1)

Here σ_t again denotes the original [0,1] parametrization. The estimate is for the original chosen side, not a side chosen by optimal transport.

Put β=3n/p and α=1/(1+β)=p/(p+3n). If δ=0, let h↓0 in (6.1), obtaining the frozen inequality with zero error. If δ>0 and z=(Bδ)^α≤1/8, choose h=z. Since Bδ h^(−β)=h, (6.1) has error at most11z. Multiplying by2 yields precisely

 d(a,σ_t)²≥(1−t)d(a,x)²+td(a,y)²−t(1−t)l²−22(Bδ)^α.

Finally, if z>1/8, the possible deficit in this squared-distance comparison is at most1: the endpoint squared distances are at most1, the subtracted t(1−t)l² term is nonnegative, and the left side is nonnegative. Since 22z>22/8>1, the same inequality follows directly. This covers every δ and every degenerate triangle, and proves the entire frozen statement.

## 7. Compatibility, strongest reduction, and exact limits of the submission

COMPATIBILITY.md constructs a smooth compact four-dimensional family with exact Hausdorff measure, unreduced RCD(0,4), a uniform lower ball-volume constant, a continuous sectional defect bounded by1 whose Lp norm tends to zero, and a negative mixed sectional curvature −2a at a fixed point. Its complete smooth metric-change calculation verifies that the hypotheses do not secretly force ρ=0. It is not a nonsmooth conformal-deformation theorem or a sharpness example.

The strongest compatible paid reduction was executed, not merely named: the global source inequality gives coarse CBB(−1); the full source heat-index and frame operations give the radial variable-defect Hessian measure; the companion's full drift/curvature-change/density construction transfers continuous majorants to every path; the classical CBB comparison inequalities give (4.1); transport density interpolation supplies actual averages. The proposed quantitative operation remaining after those paid ingredients is the combination of the singular-time radial Lp estimate, the upper-semicontinuous all-path representative, the explicit h-dependent endpoint stability estimate, and endpoint-ball averaging/optimization. No claim that any single paid index or semiconcavity step is new is made.

Actual primary comparison was not limited to titles: Gigli's distributional tensor construction and symmetries, nonsmooth Hessian/Bochner proofs, Brena–Gigli's curvature measure/polarization construction, Han's weak-convexity change of measure, BHS's variable-CD proof, GRS's density and uniqueness proofs, GT's second-order differentiation proofs, Deng's final nonbranching argument, AKP's point-side/hinge and globalization proofs, and the Eschenburg and Petersen–Sprouse comparison proofs were read in the exact extents recorded separately. Several cited intermediates remain unread, and their status is disclosed. In particular the classical radial-variable-bound operation and scalar Riccati Lp estimates are already established; the present statement is not presented as their invention. No priority or exhaustive literature-clearance claim follows from this scoped evidence.

This proof does not remove bounded continuity of ρ, the coarse pointwise amplitude bound, the finite integer dimension, exact H^n normalization, completeness, full support, unreduced RCD(0,n), or noncollapse. It does not silently replace an arbitrary Lp equivalence class by a geodesic trace. It proves one additive point-on-side inequality at the stated scale and does not assert an explicit distance to a global CBB(0) space. It does not assert optimal constants or rate. The pinned Lean endpoint has a sorry in its final theorem and supplies no proved formal support. Independent adversarial correctness and contribution reviews remain for the parent; none is assigned here.
