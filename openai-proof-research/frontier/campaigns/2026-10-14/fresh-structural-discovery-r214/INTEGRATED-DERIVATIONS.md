# Source338 symmetry construction — durable prefreeze derivations

No author theorem is frozen or nominated in this file. All Source338 operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are paid and stipulated true. The purpose is to carry compatible operations far enough to distinguish an actual remaining extension from a failed implementation. These calculations do not assign correctness, contribution, acceptance or count.

Throughout, M is connected, noncompact and complex n-dimensional, n≥1, and g is a smooth complete Kähler metric with pointwise strictly positive holomorphic bisectional curvature. K is a compact Lie group acting smoothly by holomorphic g-isometries. No curvature bound, noncollapse, volume-growth condition or initial simple connectivity is added. The metric h_t solves ∂_t h=-Ric(h), and the volume clock at a specified center p is s=-log(det h_t(p)/det g(p)). Every later use of simple connectivity comes from the paid source.

## 1. Making the source construction invariant

Start with the source's smooth proper exhaustion u satisfying u≈1+r, |du|_g≤C and |∂∂bar u|_g≤C/(1+r), where r=d_g(o,·) and o need not be fixed. Set u_K(x)=∫_K u(kx) dk, with normalized Haar measure. The orbit Ko is compact. If D=sup_k d_g(o,ko), then |r(kx)-r(x)|≤D. Thus u_K remains proper and comparable to 1+r, and differentiation under the compact integral preserves the gradient and complex-Hessian estimates, with constants now allowed to depend on D and K. No averaging of curvature tensors is used.

Use regular levels of u_K in the source's complete Hermitian approximants α_L=exp(F(u_K/L))g, where F vanishes on [0,1/2] and equals -2log(1-v) near1. Every domain and α_L are invariant. The source supplies completeness, bounded geometry for fixed L, existence and continuation intervals, and all local estimates required to pass to a global Kähler limit.

Here is the necessary invariance interface before that limit. Two scalar-potential solutions on one closed bounded-geometry interval, with the same α_L and zero initial potential, have bounded difference w and satisfy

    w_t = a^{i bar j}(x,t) w_{i bar j},
    a^{i bar j}=∫_0^1[(1-θ)K_1+θK_2]^{i bar j} dθ.

Both metrics are uniformly equivalent to α_L on the interval, so a is bounded above as a contravariant tensor relative to α_L. The proper function f=F(u_K/L) has bounded α_L complex Hessian. Consequently B=e^{At}(1+f) satisfies (∂_t-a^{i bar j}∂_i∂_bar j)B>0 for large A (depending on L and the interval). For ε>0 the bounded function w-εB tends to minus infinity at the boundary. Its positive maximum is impossible. Apply the same argument to -w and let ε decrease to0. This proves uniqueness in precisely the approximating class. It is not an assertion of global uniqueness for arbitrary unbounded-curvature Ricci flows.

For each k∈K, U_L∘k solves the same scalar problem, hence U_L∘k=U_L. All approximate flows are invariant. Their one locally smooth diagonal limit is invariant for every k, because the exact identities hold before taking the limit. No group-dependent subsequence is selected. The rest of the paid disc, variation, ellipsoid, completeness, Harnack, Ricci-window and chart constructions can be applied to this limit. Estimates may use noninvariant auxiliary barriers; that does not change the already constructed flow.

## 2. Common fixed point: integrate the Chau–Tam operation

This follows the actual mechanism of Chau–Tam 0806.2457v1, §2, Theorems2.4–2.5, using the stronger geometric inputs now supplied by Source338. It is not a new fixed-point method.

The source's selected times give complete metrics g_i=R(o,t_i)h_{t_i}, invariant scalar functions r_i=R(h_{t_i})/R(o,t_i), constants a,r_*>0, and ε_i→0 such that

    Hess_{g_i} r_i ≤ -a g_i on B_{g_i}(o,2r_*),
    |grad_{g_i}r_i|(o)≤ε_i,       R(o,t_i)≤C.

On a radial minimizing geodesic of length r≤2r_* the outward derivative is at most ε_i-ar. Therefore r_i attains its maximum on the closed ball of radius r_* at an interior point q_i, and d_i(o,q_i)≤ε_i/a. Completeness supplies compactness of this closed ball; the radial derivative rules out a boundary maximizer, including at a cut point by following a minimizing segment inward.

There is at most one critical point in B_i(o,r_*/2). A minimizing segment between two such points has length at most r_* and stays in B_i(o,3r_*/2); strict Hessian negativity would make the directional derivative strictly decrease from0 to0, a contradiction.

The original orbit Ko lies in a fixed compact g-ball. Initial minimizing geodesics from o to its points lie in a larger fixed compact set. Source compact metric decay, together with the uniform upper bound for R(o,t_i), gives

    δ_i:=sup_{k∈K} d_i(o,ko) →0.

Every kq_i is again critical and d_i(o,kq_i)≤δ_i+ε_i/a. For all sufficiently large i this is less than r_*/2, so uniqueness gives kq_i=q_i simultaneously for all k. Choose one such point p once. No convergence of q_i in the original metric is assumed or needed.

## 3. Equivariant uniform immersed charts and coherent inverse branches

Fix a g-unitary frame T_pM≅C^n and the unitary isotropy representation ρ:K→U(n). The positive Hermitian endomorphism representing h_t(p) commutes with ρ. Its positive inverse square root therefore supplies an h_t-unitary frame in which the matrices ρ(k) remain the same at every t.

On the fixed small tangent ball used in source Lemma chart:local-charts, the exponential map E_t is K-equivariant. Its pullback complex structure J_t is invariant under ρ; it need not be standard away from0. The source proof supplies J_t-holomorphic coordinates χ_t on a fixed real ball, with χ_t(0)=0, dχ_t(0)=I after a bounded linear normalization, and uniform C² bounds on a smaller ball. Average the coordinate functions, not the maps M→M:

    χ̃_t(v)=∫_K ρ(k)^{-1}χ_t(ρ(k)v) dk.

They remain J_t-holomorphic. Their derivative at0 is I and the same C² bound holds. On a uniformly smaller ball, dχ̃_t stays within1/2 of I. The quantitative inverse function argument supplies an inverse on one fixed Euclidean ball. Then Φ_s=E_t∘χ̃_t^{-1} is an equivariant holomorphic local biholomorphism with all uniform metric/derivative bounds needed in source Proposition prop:shrinking-charts. It can be immersed rather than globally injective.

The source's short-path lifting and simple-connectivity proof consequently applies to these charts themselves. Choose connected K-invariant relatively compact exhaustion neighborhoods D_m containing p: replace any connected neighborhood by its K-saturation; each translate contains p, so the saturation is connected and has compact closure. For all s≥T_m there are inverse branches f_s on D_m, coherent on overlaps, with

    Φ_s f_s=Id,    f_s(p)=0,    sup_L |f_s|≤e^{-σs}

for each fixed compact L and all sufficiently large s, with one σ>0 and compact-dependent onset. Equivariance follows from equality of inverse germs at p followed by analytic continuation on D_m:

    f_s(kx)=ρ(k)f_s(x).

This is simultaneous in k, since the domain D_m is invariant. The transition germs F_{s,u} commute with ρ, have common domains/bounds, compose coherently, and retain the source estimates for determinant, inverse linear part, jets and exponentially small input balls. No common global injectivity radius is inferred.

## 4. Complex-time continuation closes, but is classical

For ξ∈Lie(K), let A=dρ(ξ). On any fixed compact L⊂M and complex-time disc |z|≤T, take s large enough that e^{T||A||}sup_L|f_s| is less than the chart radius. Then

    c_s(z,x)=Φ_s(exp(zA)f_s(x))

is jointly holomorphic on a neighborhood of that disc times L, starts at x, and solves the holomorphic vector-field equation for the infinitesimal action. The equation follows first by differentiating equivariance for real time and then by holomorphic continuation. Uniqueness of the local holomorphic ODE makes these formulas agree when s or T changes. Every infinitesimal K-action field is therefore complex-complete. This argument explicitly controls a whole compact set of initial conditions, not just one orbit at a time.

There is no new completeness theorem here. The actual original proof of Forstnerič, Math.Z.223(1996), §2, was read visually. For a real-complete holomorphic field on a Stein manifold, maximal complex times form strips R+i(-b(x),a(x)), and -a,-b are negative psh. On C^n they are constant; iterating a uniform imaginary-time interval makes them infinite. Hence real-complete implies complex-complete on C^n, without any isometry hypothesis. Source338 transfers this directly. Derksen–Kutzschebauch explicitly applies this interface to compact-group complexification. No assertion that the extended complex action is isometric is made.

The chart formula has bounds only after a compact-dependent clock threshold. It does not supply a bound for the original g-distance of a complexified orbit, a quasi-isometry, or a globally controlled derivative for a uniformization.

## 5. Fixed loci: another complete compatible reduction, not a nominee

For every closed subgroup H≤K, the fixed locus M^H is a smooth complex submanifold by local averaged coordinates. It is totally geodesic: an initial tangent vector fixed by H yields an H-fixed ambient geodesic by uniqueness. Its induced metric is complete and inherits strictly positive bisectional curvature through the totally geodesic Gauss formula.

It is connected. Given x∈M^H, use the equivariant inverse branch f_s on a connected invariant neighborhood containing p and x. Its value f_s(x) lies in the fixed vector subspace (C^n)^H and eventually lies in the chart ball. The path t↦Φ_s(t f_s(x)), 0≤t≤1, lies in M^H and joins p to x. No global injectivity of Φ_s is needed for this path.

Its complex dimension is dim(T_pM)^H. If positive, it cannot be compact, since the paid uniformization M≅C^n supplies a strictly psh exhaustion on M and excludes a compact positive-dimensional complex submanifold. Apply Source338 to the complete connected induced metric: M^H≅C^{dim(T_pM)^H}. In dimension0, connectedness says it is the single point p. This does not straighten its embedding in M, compare its induced metric with Euclidean metric, or linearize the whole action. The argument consists of the paid chart construction, fixed-locus geometry and another application of the paid theorem.

## 6. A genuine obstruction to naive equivariant jet realization

For circle weights (1,-1), write u=zw. Every equivariant holomorphic germ fixing0 has form (z a(u),w b(u)). If it is a polynomial automorphism, its induced automorphism of the invariant polynomial ring C[u] fixes0, so u a(u)b(u)=c u. Polynomial a,b must therefore be constants. Nevertheless (z exp(u),w exp(-u)) is an entire equivariant automorphism of determinant1 with a nonzero cubic term. Thus the source's polynomial constant-volume jet realization cannot simply be made equivariant by averaging the shear list.

For coprime positive integers p,q and weights (p,-q), put u=z^q w^p. Every equivariant entire automorphism fixes both axes and has form (z a(u),w b(u)), with

    u a(u)^q b(u)^p=c u.

The induced map on the invariant holomorphic quotient C is an automorphism fixing0. The factors are nowhere zero, so after normalization a=a_0 exp(pP), b=b_0 exp(-qP) for an entire P with P(0)=0. Its determinant equals a_0b_0 exp((p-q)P). When p≠q, a constant determinant forces P=0. Thus allowing entire automorphisms still does not realize every equivariant constant-volume jet in unequal weights.

For example, the equivariant divergence-free polynomial field

    X=( (p+1)z u, -(q+1)w u )

has div X=0 and induces u'=(q-p)u². Its local time-one germ has constant determinant1 and nontrivial quotient jet; no equivariant entire automorphism can realize that quotient jet. This is a limitation of that jet interface, not a proof that equivariant uniformization is impossible. The next calculation bypasses it.

## 7. Balanced weights: exact entire replacement and exhaustion

For weights (1,-1), det D(z a(u),w b(u))=(u a(u)b(u))'. A constant determinant δ therefore implies ab=δ. The germ is exactly

    (a_0 z exp P(u), b_0 w exp(-P(u))),       a_0b_0=δ,

with P a holomorphic germ vanishing at0. Truncating P at degree m yields an entire automorphism realizing its component jets through degree2m+1. The inverse is explicit:

    (Z,W)↦(a_0^{-1}Z exp[-P(ZW/δ)], b_0^{-1}W exp[P(ZW/δ)]).

The source's coherent volume correction is already equivariant in this representation. Its invariant Jacobian jet E_k(u) gives A_k(z,w)=(z,w h_k(u)), where h_k(u)=u^{-1}∫_0^u E_k(v)dv. This is exactly the source's last-coordinate integral, not a new correction. Hence normalized transition jets can be realized by the entire models above.

Suppose the model coefficients satisfy the source-scale bound ||P_k||≤exp(C_m Δs_k+o(s_k)), P_k(0)=0, with fixed degree m, and choose macro width so C_m(e^h-1)<1/4. Write a_kb_k=δ_k, D_j=∏_{l<j}δ_l, A_j=∏_{l<j}a_l, B_j=∏_{l<j}b_l. Then

    G_{0,k}(z,w)=(A_k z exp S_k(u), B_k w exp[-S_k(u)]),
    S_k(u)=Σ_{j<k} P_j(D_j u),     |D_j|=exp(-(s_j-s_0)/2).

For every fixed R and every derivative order, the j-th summand on |u|≤R is bounded by C_{R,m}exp(-s_j/4+o(s_j)), since P_j has no constant term. Grid spacing eventually≥1 makes this summable. Thus S_k converges with every derivative, locally uniformly; it is even a polynomial of degree≤m. The source's long-transition derivative bound gives |A_k|+|B_k|≤C_{s_0}e^{-σs_k}. Consequently G_{0,k} tends to0 on every fixed compact set at rate C_L e^{-σs_k}.

On exponentially small balls, P_k and its differentiated factors are small if h is chosen after m. The explicit inverse has derivative bounded by exp(Δs_k/2)(1+o(1)), hence by exp(Δs_k) eventually. High-order jet agreement gives the same summable defects as in source backward shadowing. Its local limit construction, injectivity and inverse-ball inclusion use these estimates and global existence of G_k^{-1}; they do not require polynomial behavior at infinity. The source's final polynomial-degree argument can therefore be replaced here by the displayed forward formula: if

    G_{0,k}^{-1}(B(e^{-γ's_k}))⊂Ω,        0<γ'<σ,

then every fixed y∈C² eventually satisfies G_{0,k}(y)∈B(e^{-γ's_k}), hence y∈Ω. This carries surjectivity through, rather than merely asserting a normal family. The unchanged backward estimates also carry the inverse maps. This special representation supplies a genuine repair of the failed polynomial route, but not a general-group construction.

## 8. Unequal weights: straighten the quotient before realizing jets

The obstruction in §6 is not the last compatible reduction. Here is a finite-order construction that avoids requiring constant volume. It explains why that obstruction alone cannot be an unpaid theorem.

Use the equivariant source charts in complex dimension2 with fixed weights (p,-q), p,q>0, and choose a geometric clock grid s_{k+1}=(1+η)s_k. Put μ=min(p,q), M=max(p,q). The transition F_k=(z a_k(u),w b_k(u)) induces a one-variable germ φ_k(u)=u a_k(u)^q b_k(u)^p. For δ_k=φ_k'(0), the source linear normalization gives

    exp(-MΔs_k/2)≤|δ_k|≤exp(-μΔs_k/2).

On one fixed disc in u, each fixed collection of unnormalized coefficients of a_k,b_k and φ_k is bounded independently of k, by Cauchy estimates on the fixed chart ball. This assertion involves only finitely many coefficients, and does not divide by their small center values.

To any prescribed finite quotient order m+1, construct h_k(u)=u+Σ_{r=2}^{m+1}c_{k,r}u^r such that

    J_{m+1}(h_{k+1}∘φ_k)=δ_k h_k.

At order r this is

    c_{k,r}=δ_k^{r-1}c_{k+1,r}+b_{k,r},
    b_{k,r}=δ_k^{-1}([φ_k]_r+Σ_{j=2}^{r-1}c_{k+1,j}[φ_k^j]_r).

Choose recursively constants L_r independent of sufficiently small η, large enough to dominate M/2+2max_{j<r}L_j and all finite coefficient constants. Assuming the lower-order bounds |c_{k,j}|≤C_j exp(L_jηs_k), one gets |b_{k,r}|≤C_r exp(L_rηs_k). The future-tail solution is

    c_{k,r}=Σ_{l≥k}(δ_k⋯δ_{l-1})^{r-1}b_{l,r}.

Its l-th term is at most C_r exp[-μ(r-1)(s_l-s_k)/2+L_rηs_l]. Choose η after the finite order so L_rη<μ(r-1)/4 for all r. Since the clock gaps eventually exceed1, this series is absolutely convergent and bounded by C'_r exp(L_rηs_k). It solves the recursion by shifting the sum. This is a concrete bounded tail construction, not a parameterwise choice without compatibility.

Lift h_k to an equivariant local coordinate change

    H_k(z,w)=(z,w (h_k(u)/u)^{1/p}),

using the branch equal to1 at0, and retain the finite component jet needed. Its coefficients and inverse jet are bounded by exp(C_mηs_k). In these coordinates the quotient jet is δ_k u. Therefore the transformed component jets satisfy q log(a/a_0)+p log(b/b_0)=0 to the required order, and can be realized by

    G_k(z,w)=(a_{k,0}z exp[pP_k(u)], b_{k,0}w exp[-qP_k(u)])

with polynomial P_k, P_k(0)=0, fixed degree, and coefficient bound exp(C_mηs_k). Their inverses are entire, with u replaced by u/δ_k. These maps need not have constant Jacobian. No use of the invalid equivariant constant-volume realization remains.

The composition formula of §7 persists with pS_k and -qS_k, and now |D_j|≤exp(-μ(s_j-s_0)/2). Choosing C_mη<μ/4 makes S_k=ΣP_j(D_j u) locally uniformly convergent with every derivative. The unchanged component linear products A_k,B_k still equal the source's long-transition center derivative, so they contract at rate e^{-σs_k}. This gives forward shrinking on every compact of C² and the same onto argument once backward shadowing has been carried out.

For clarity about that local estimate, choose 0<γ'<γ<σ and a jet degree d with (d+1)3γ/4>12. Only then choose η so every finite coefficient exponent C_dη is less than γ/8, and (C_d+M/2)η<γ/2. On a ball of radius exp(-γs_k/4), all H_k and model exponentials are controlled; on the smaller radius exp(-γs_k), Cauchy's remainder estimate makes a defect vanishing to order d+1 at most exp(-10s_k), after increasing the starting threshold. On the inverse tubes at clock s_{k+1}, the argument u/δ_k in P_k has size at most exp(MΔs_k/2-(p+q)γs_{k+1}); the chosen η makes both P_k and the extra derivative factors tend to0. Thus ||DG_k^{-1}||≤exp(Δs_k) there. The source's summable backward construction and inverse-ball inclusion apply with these bounds. This supplies the local and global estimate interfaces for the unequal-weight repair; no uniform-in-(p,q) constants are asserted.

## 9. What is and is not left

The complexification proposal is absorbed by the actual Forstnerič proof. Common compact-group fixed points follow the actual Chau–Tam mechanism once the source supplies invariant flow and selected-window concavity. Fixed-locus uniformization is a compatible source/classical composition. In the two-dimensional mixed-weight circle case, the naive model obstruction is bypassed by quotient straightening and entire overshears; it is not an unresolved obstruction to that case. Published Derksen–Kutzschebauch Theorem2.2 attributes the broader linearization of circle actions on C² to Suzuki plus Forstnerič; the Suzuki proof is being checked separately, so this attribution is not a worldwide priority clearance.

For an arbitrary compact K and arbitrary dimension, no construction here supplies K-equivariant global models with both compatible jets and the required forward/inverse exhaustion. The source's polynomial models and approximation theorems are already fully paid, but their equivariance is an additional demand. The finite-dimensional shear spanning proof is not automatically a spanning proof by complete K-invariant fields. The two-weight quotient repair shows why a single missing jet realization is insufficient to declare the general target blocked. Higher-dimensional invariant quotients can be singular and have coupled transition maps; no simultaneous quotient normalization or alternative global equivariant construction has been proved here. We have no counterexample carrying the required invariant positive-bisectional metric, and no impossibility or exhaustion claim.

Accordingly this remains PREFREEZE/no nominee. No narrower theorem is substituted for a frozen target: there was no frozen statement. The original explorations and their obligations remain recorded.

## 10. Original Suzuki endpoint now read

Suzuki, Ann.Sci.ÉNS10(1977), §III nos6–7, gives Theorem5 explicitly: every holomorphic C* action on C² is analytically equivalent to (λ^m z,λ^n w), m,n∈Z. The operative classification proof preceding it reduces a meromorphic first integral via Saito's form, analyzes the C and C* generic-fiber cases, and constrains the orbitwise exponential rate; global periodicity forces integral weights. Theorem5 also invokes Suzuki's earlier [14] result. The original nos8–11 and the cited Nishino/Saito/[14] intermediate proofs have not all been read, so this is precise endpoint/proof-interface reading, not a complete rereading of its entire antecedent chain.

The strongest compatible reduction for circle actions on a Source338 surface is consequently complete: choose the paid uniformization Ψ:M→C²; transfer the given S¹ action; extend it by Forstnerič; apply Suzuki's full C* classification; compose the resulting linearization with Ψ. At the common fixed point, its derivative intertwines the two tangent representations. A final linear change identifies the resulting representation with the prescribed isotropy representation. This realizes the entire mixed-weight equivariant conclusion of §§7–8 by classical operations. The explicit model construction remains useful as durable compatibility work but is not submitted as a new result. The general-dimensional compact-group linearization question is not thereby settled.

## 11. Late strongest comparison: the full Chau–Tam normal-form mechanism

After the prefreeze calculations above, all mathematical sections1–5 of Chau–Tam math/0504422v3 were read, including the full normal-form and exhaustion proof. This is a late comparison, not an earlier premise silently inserted into the exploration. Their operative setting is complete noncompact Kähler with bounded nonnegative holomorphic bisectional curvature, uniform quadratic average scalar-curvature decay, and maximal volume growth; their positive-curvature-operator alternative removes the volume-growth hypothesis. Their Ni-based corollary removes the separately stated decay assumption under maximal volume growth. None of these extra quantitative assumptions is inferred from the strictly positive pointwise bisectional curvature of Source338.

The normalized flow is g(t)=e^{-t}g̃(e^t), satisfying ∂_t g=-Ric(g)-g. Sections3–4 prove limiting Ricci eigenvalues, uniform convergence on asymptotic tangent subspaces V_j, asymptotic orthogonality, dimension matching and the determinant identity. The proof uses soliton limits, spectral projections and a strict drift of normalized vectors toward the slower-decaying spectral blocks; it does not merely choose a convergent matrix subsequence. On a fixed time grid, chart transitions have uniform two-sided contraction a|v|≤|A_i v|≤b|v|, 0<a<b<1, and approximately fixed block rates τ_j. Their Lemma5.3 splits each homogeneous error into a strictly lower-triangular term Q and a convergent future homological sum H. For degree m above m_0, a^{-1}b^m<1/2 eliminates Q entirely. For smaller m, every term involving a block j≥k in output block k has the spectral ratio needed for the same convergent sum. The remaining terms depend only on earlier blocks and hence define triangular polynomial automorphisms.

This already supplies an equivariance-preserving construction when these flow/splitting inputs are available. To check compatibility, use the invariant flow and charts of §§1–3 at a common fixed point. Each V_j is characterized by its asymptotic norm rate; K preserves the norms, so it preserves V_j and its g(0)-orthogonal complements. The corresponding time-dependent chart subspaces are K-invariant. Multihomogeneous projection with respect to those blocks, projection to the output block, restriction to earlier input blocks, and multiplication by A_i or A_i^{-1} all commute with K. Therefore the Q and H of Lemma5.3 remain equivariant whenever their input error does. Its convergent infinite sums remain equivariant as well. Induction in Lemma5.4 produces equivariant coordinate jets T_i and equivariant triangular global models G_i; no averaging of global automorphisms or of complete fields is needed.

The rest must also be carried. Lemma5.5 recursively solves the triangular inverse, with uniform degree and coefficient bounds. Lemma5.6 bounds inverse-composition derivatives on a fixed ball by β^l and proves G_{i+l}⋯G_{i+1}→0 on every compact by induction over blocks. Choose the jet order after β so the forward-contraction error δ^{ml} beats β^l. Lemma5.7's telescoping series then converges uniformly on a fixed ball, its derivative at0 is I, and it has a uniform inner image ball. Injectivity follows by pushing any pair into the common small injectivity ball and conjugating back. Finally the metric chart domains exhaust M, while the inverse model images of that inner ball exhaust C^n. Every term is equivariant, so the limit is equivariant and onto. This credits the entire compatible operation, including global images and inverse estimates.

Thus even a general-K conclusion with these extra classical flow/splitting inputs would be a source/classical composition, not the distinct full-scope result sought here. The still unproved extension is to construct a compatible equivariant model/assembly for the full Source338 setting, without importing fixed Lyapunov block rates, uniform step contraction, maximal volume growth, or bounded original curvature. The variable-clock source dynamics already handles their absence for ordinary uniformization. The work here has not shown that its global polynomial model realization can be replaced equivariantly for every compact representation, nor that a different invariant construction closes the same full scope. This is a precise limitation of these derivations, not a claim that the source lacks an ordinary uniformization estimate or that the general symmetry statement is false.
