# Source351: executed reductions and prospective nonlinear continuation

Research notes, Structural r227. Codex / GPT-6 Astra / xhigh / default service tier. These are prefreeze derivations, not a frozen author-proof nominee and not a correctness or contribution decision. All three Source351 manuscripts and their operative upstream proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are accepted as true. Their difficult operations are paid inputs. Constants below may depend on the one selected flow; no uniformity over k, q, initial metrics, or moduli is asserted.

## 1. Exact geometric setting and the available estimates

Use one of the supplied unnormalized flows ∂_t g = −2 Ric on the fixed smooth closed connected manifold M = S² × S^(q+1), real dimension n=q+3. Its maximal time T is finite. Set δ=T−t, θ=δ^σ, σ=k/d, ν=k−d/2, where k is a sufficiently large even integer and d=(q+1−sqrt((q+1)(q−7)))/2. The supplied choices have 2<d<a=5/2, ν>1, σ>1/2, and

    e = a−d+d/k ∈ (0,1),     σ(a−e)=k−1.

At a fixed late time, on either hemisphere the metric is

    g = ds² + φ² g_(S²) + r² g_(S^q),    v=r_s>0.

At a pole r=0, v=1, φ_s=0, and φ>0 before T. Norms in these notes are in g(t). Scalar curvature R, the Ricci tensor Ric, and full Riemann curvature Rm are distinct throughout.

The operative construction, cap, geometry, reaction, and barrier sections supply, for late t:

1. |R|≤C, cθ≤φ(0,t)≤Cθ, bounded |φ_s| and |r_s|, and φ/r≥c globally away from a pole.
2. On r≤sqrt(δ), v is bounded above and bounded away from zero; in particular |z−1|≤4/q, z=v². The smaller interval r≤Y₁θ also has φ≥cθ. The cap estimate and φ/r lower bound combine to give φ≥c(θ+r) on r≤ξ sqrt(δ), with ξ the fixed source barrier radius.
3. Globally (r²+θ²)|Rm|≤C.
4. On r≤ξ sqrt(δ),

       |Ric| ≤ C δ^(k−1)(r²+bθ²)^(−a/2)
             = C θ^(a−e)(r²+bθ²)^(−a/2),     b>0 fixed.

5. On the entire exterior r≥ξ sqrt(δ), |Ric|≤C. This includes the equator and both hemispheres; it is the proved geometric exterior proposition, not merely a fixed parabolic annulus estimate.
6. On Y₂θ≤r≤ξ sqrt(δ), the actual profile bounds imply

       |z−B²|≤C(θ/r)^d,       B²=(q−1)/(q+1)<1.

To verify (6), γ=r/sqrt(δ) lies in (0,ξ], on which Z_k and the error weight are bounded by Cγ^(−d). Then δ^ν γ^(−d)=δ^(ν+d/2)r^(−d)=θ^d r^(−d). There is no need to improve the source's fixed tolerances to a vanishing matching remainder.

All later deductions use these estimates at their actual scope. In particular, no Ricci-flat cap limit, asymptotic amplitude, unique cap, or modulation limit is assumed. Those are the distinct old sharp-cap questions encountered in the admitted original history section; they are not reopened here.

## 2. The cap measure, including its non-Euclidean small-radius regime

Since ds=dr/v, bounded φ_s and v≥c give

    φ(r,t) ≤ φ(0,t)+C r ≤ C(θ+r).

Together with (1)–(2), this proves φ≈θ+r on 0≤r≤ξ sqrt(δ). After integrating the two spherical factors, the volume element there satisfies

    dμ_t ≈ (θ+r)² r^q dr = (θ+r)² r^(n−3) dr.

Hence, writing D_ρ(t) for the union of the two pole regions {r<ρ},

    μ_t(D_ρ(t)) ≈ θ² ρ^(n−2)+ρ^n,    0<ρ≤ξ sqrt(δ).

The constants include the two poles. For ρ≪θ this is θ²ρ^(n−2), not ρ^n. Thus an assertion of Euclidean r^n growth at every orbit radius would be false. For θ≤ρ≤ξ sqrt(δ), the measure is comparable to ρ^n. In particular the θ-scale cap has volume comparable to θ^n even though its very small radial subregions have a surviving S² factor.

## 3. Global propagation of the orbit-radius volume upper bound

A purely inner computation would leave a gap in a global weak-L^(n/2) claim. The strongest available exterior Ricci estimate closes that gap, together with the scalar volume equation. This argument is written in material coordinates, not in the time-dependent arclength gauge.

The fixed group action identifies the function r(x,t) intrinsically as the S^q orbit radius at a material point. Let χ(x,t) be the Ricci eigenvalue on an S^q tangent unit vector. Since g restricted to those directions is r² g_(S^q),

    ∂_t log r(x,t) = −χ(x,t),       |χ|≤|Ric|.

Let E_t={r≥ξ sqrt(T−t)}. On E_t, |χ|≤C_E. At sufficiently late t,

    ∂_t log(r/(ξ sqrt(δ))) = −χ + 1/(2δ) > 0

whenever r/(ξ sqrt(δ))≥1. The first crossing argument shows that E_t is forward invariant along material points. A point that is exterior at time s remains exterior for every u∈[s,t]. Consequently

    e^(−C_E(t−s))r(x,s) ≤ r(x,t) ≤ e^(C_E(t−s))r(x,s)

on such a trajectory. This uses neither a sectional curvature bound nor a global arclength coordinate.

Fix t₀ late enough for all the preceding statements. Choose A>exp(C_E(T−t₀)), put c_A=(A/ξ)², and choose ρ₀>0 with c_Aρ₀²≤T−t₀. For ξ sqrt(δ)≤ρ≤ρ₀ set s=T−c_Aρ²; thus t₀≤s≤t. If a point x in D_ρ(t) were in E_s, forward invariance would imply

    Aρ = ξ sqrt(T−s) ≤ r(x,s)
       ≤ exp(C_E(t−s))r(x,t) < Aρ,

a contradiction. Therefore, as sets of material points,

    D_ρ(t) ⊂ M\E_s = D_(ξ sqrt(T−s))(s).

The scalar bound gives the pointwise density comparison

    dμ_t/dμ_s = exp(−∫_s^t R(x,u)du) ≤ exp(C_R(T−t₀)).

The inner measure calculation at time s now gives

    μ_t(D_ρ(t)) ≤ C μ_s(D_(ξ sqrt(T−s))(s))
                ≤ C (T−s)^(n/2) ≤ Cρ^n.

For θ≤ρ≤ξ sqrt(δ), section 2 supplies the same upper bound directly. For ρ≥ρ₀ it follows, with a larger constant, from the global volume bound resulting from |R|≤C. We have thus derived

    μ_t(D_ρ(t)) ≤ Cρ^n for every ρ≥θ(t),

uniformly for late t. This is a statement about orbit-radius sublevel sets; it does not assert a volume comparison theorem for arbitrary metric balls, noncollapse, injectivity-radius control, or a smooth limit.

## 4. Global curvature distribution and the exact integral thresholds

Write K=|Rm| and F_p(t)=∫_M K^p dμ_t. From the source full-curvature bound,

    {K>λ} ⊂ D_(sqrt(C/λ))(t).

If λ>Cθ^(−2), the set is empty after increasing C. Otherwise sqrt(C/λ)≥θ, so section 3 applies. The bounded total volume handles small λ. Therefore

    μ_t{K>λ} ≤ min(V₀, C λ^(−n/2))

for every λ>0 and all late times. In particular K has a uniformly bounded weak-L^(n/2) norm with respect to the evolving measure.

This weak estimate cannot be upgraded to a bounded strong critical norm for these flows. Choose a fixed Y≥Y₂ large enough that C Y^(−d)≤(1−B²)/2 in estimate (6). On the genuine nonempty annulus

    Yθ≤r≤ξ sqrt(δ),

we have 1−z≥(1−B²)/2. It is nonempty for all sufficiently late t because σ>1/2. The S^q tangential sectional curvature is ℓ=(1−z)/r², so K≥c/r². Also φ≈r and v≈1 there, hence dμ_t≈r^(n−1)dr. The same annulus supplies matching lower bounds without assuming cap-profile convergence.

Layer-cake integration of the distribution upper bound, followed by these annular lower bounds, gives:

* 0<p<n/2: F_p(t)≤C_p.
* p=n/2: c|log δ|≤F_p(t)≤C(1+|log δ|).
* p>n/2: c_p θ^(n−2p)≤F_p(t)≤C_p θ^(n−2p).

For the critical lower bound, integrate r^(−1) from Yθ to ξ sqrt(δ). This is

    (σ−1/2)|log δ| + log(ξ/Y).

For the supercritical lower bound, the fixed-scale annulus [Yθ,2Yθ] suffices. For the upper bound at p=n/2 the layer-cake integral is O(log θ^(−1)); no equality of leading logarithmic coefficients is claimed. For p>n/2 the upper integral is O(θ^(n−2p)). Earlier times are smooth and compact and add finite constants.

For finite p>n/2 and finite s>0, these two-sided bounds show

    ∫^(T) ||Rm(t)||_(L^p)^s dt < ∞
        ⇔ σ s(2−n/p)<1.

At equality the integral diverges logarithmically. At p=n/2 every finite temporal power of the spatial norm is integrable, although its supremum is not bounded. In the spacetime case s=p, the exact threshold for p>0 is

    ∫_0^T∫_M |Rm|^p dμ_t dt < ∞
        ⇔ p < p_* := n/2 + 1/(2σ).

At p=p_* divergence is logarithmic. Since σ>1/2, p_*<(n+2)/2. The family with k tending to infinity in fixed sufficiently large dimension has p_* decreasing to n/2, but these are different flows. Nothing here creates a single flow with arbitrary rates.

These global estimates execute an integrated consequence of the source cap, profile, full-curvature, scalar, and exterior-Ricci operations. They are retained as concrete mathematics, but the task's acceptance rule does not allow calling a difficult paid composition substantial merely because several paid inputs occur in it. They are not submitted as a nominee.

## 5. Ricci integrability, separately from curvature integrability

Let I_p(t)=∫_(r≤ξ sqrt(δ)) |Ric|^p dμ_t. The sharper source barrier, rather than merely |Ric|≤Cr^(−e), yields

    I_p ≤ C θ^(p(a−e)) ∫_0^(ξ sqrt(δ))
                      (r²+bθ²)^(−ap/2)(θ+r)²r^(n−3)dr.

Splitting at θ gives the following upper bounds:

    ap>n:  I_p ≤ C θ^(n−ep);
    ap=n:  I_p ≤ C θ^(n−ep)(1+log(sqrt(δ)/θ));
    ap<n:  I_p ≤ C θ^(p(a−e)) δ^((n−ap)/2).

The cap term in the last line is no larger than the displayed term, since θ≤sqrt(δ). In the middle line n−ep=(a−e)p>0. It follows that I_p→0 for every p<n/e, and I_(n/e)≤C. At this endpoint ap>n because a>e, so there is no logarithmic loss. The exterior Ricci estimate and bounded global volume then imply

    sup_(t<T) ∫_M |Ric|^(n/e) dμ_t < ∞.

This exponent exceeds n. It is a spatial integral bound, not a pointwise bound. More generally, the same calculation gives finite spacetime ∫|Ric|^p for every

    0<p<(n+1/σ)/e.

There is no matching lower Ricci estimate here, so no assertion of sharpness at that latter threshold is made. In particular no divergence is inferred from an upper bound.

Compatibility with time-integrated pointwise continuation tests must be checked. The source upper bound at the cap is |Ric|≤Cθ^(−e), and

    σe = σ(a−d)+1 > 1.

Thus this estimate does not imply an integrable L^∞ Ricci norm in time. It cannot be used as a hidden smooth-extension argument. Separately, the scalar evolution equation gives

    d/dt ∫_M R dμ_t = 2∫_M |Ric|² dμ_t − ∫_M R² dμ_t.

Bounded R and volume imply a finite spacetime L² Ricci integral, but that weaker statement alone supplies neither the higher exponents above nor pointwise Ricci control.

## 6. Compatibility of geometric parameters: the Einstein-fiber route

The original Stolarski construction starts with a closed positive Einstein p-manifold (N,h), Ric_h=(p−1)h, and a doubly warped metric

    ds²+φ²h+r²g_(S^q).

Its warping Ricci equations depend on h only through the displayed Einstein constant and p. The actual primary proof explicitly reduces the construction to the round S^p case for this reason. The topology N×S^(q+1) and this transfer are already paid classical/primary operations, not a new implantation theorem.

The exact supplied bounded-scalar refinement has p=2. In real dimension two, Ric_h=K_h h, hence Ric_h=h forces K_h≡1. A closed such surface is a spherical space form. For a connected smooth closed surface the universal cover is the unit S²; a free isometric quotient is either S² itself or RP² (the orientable case is S²). Indeed a nonidentity orientation-preserving isometry of S² has a fixed axis, so a free finite group injects into the two-element orientation-sign group; a free orientation-reversing involution must be the antipodal map. Thus p=2 does not provide a free local moduli parameter of normalized Einstein metrics. A putative arbitrary Einstein-fiber family in this exact source setting is empty beyond these discrete choices and diffeomorphism pullbacks. This explicitly checks the compatibility condition in the brief.

For p>2 the same Einstein transfer remains an operation of the original construction, but the supplied bounded-scalar refinement has not been restated for arbitrary p here. Proving all p-dependent reaction constants and barrier margins would be a further argument, and the primary fiber replacement would remain paid within it. Arbitrary topology changes, open-set stability, and global parameter selectors do not follow from this observation.

### 6a. An actual outer parameter, and the paid relative degree construction

A late read of the initial-data construction (BoxDefn.tex75–386, omitting inactive comment326) supplies a stronger compatible alternative than the Einstein-fiber route. This reduction is recorded as a paid classical/source composition, not a newly frozen theorem or contribution claim.

At the initial time the original construction first fixes the exact eigenprofile and shooting expansion on the parabolic annulus. It then chooses the outer r(s), and extends φ by

    (log φ)_s = f(s) r_s/r,

where 1≤f≤2, the matching jets are fixed at the inner end, all odd jets vanish at the equator, and f_s is bounded. Choose the extension with 1<f₀<2 on a closed interior subinterval I on which r_s>0. This is possible because the proof allows a smooth interpolation on that interval while fixing its endpoint jets. Choose a nonzero nonnegative smooth h supported strictly inside I, and set

    f_λ=f₀+λh,    |λ|≤ε,
    H(s)=∫_(s₀)^s h(u) r_s(u)/r(u) du,
    φ_λ(s)=φ₀(s) exp(λH(s)).

Take ε||h||_∞ smaller than the distance of f₀(I) to {1,2}. Then 1≤f_λ≤2, all matching jets are unchanged, H=0 before I, H is constant near the equator, and reflection produces smooth closed metrics. The source's outer sign, slope and curvature bounds remain valid with common enlarged constants on this compact λ interval. The inner and parabolic data have not changed. This is an explicit nonempty parameter domain, not an asserted free Einstein modulus.

For fixed shooting coefficients, r and ds are fixed. Consequently

    d/dλ Vol(g_λ) = 2∫_M H dμ_(g_λ) > 0.

For a sufficiently late starting time, the unchanged pole has curvature at least cθ₀^(−2), whereas the whole perturbed outer region has curvature at most Cδ₀^(−1). Since θ₀²/δ₀→0, the maximum of |Rm| lies in the unchanged region and is independent of λ. Thus the fixed-coefficient metrics are pairwise nonisometric, and cannot be related by a nontrivial constant rescaling followed by an isometry: their common positive maximum curvature fixes the rescaling factor, while their volumes differ. This proves actual geometric freedom at the initial-data level. It does not assume anything about the shooting coefficients later chosen as a function of λ.

The construction can be made smoothly for the whole finite-dimensional shooting ball: use fixed buffer intervals and the same outer h after matching the parabolic data, with bounds enlarged uniformly on the compact parameter set. The exact parabolic eigen-expansion is untouched, and the source's initial projection errors still have the proved inner/outer bounds. The source estimates depend on the displayed constants and cutoffs, not on the particular f used in that extension. Choose all tolerances and cutoffs uniformly in the same required order, then increase the starting rescaled time once. This is the important compatibility step; adding an arbitrary bump directly to the exact parabolic eigen-expansion would not preserve Definition3.5 and is not used.

For each finite terminal rescaled time b, let Ω_b be the admissible open set of pairs (λ,c), where c denotes all lower U/Z shooting coefficients and the solution exists to b within the source box. Let P_b(λ,c) be the source's terminal lower-mode projection map. The source's finite-time dependence and zero-in-the-interior estimates, with the common constants just described, give the same nonzero degree on every λ fiber and a compact zero set Z_b contained in Ω_b. In particular no new uniqueness or invertibility assumption has been inserted.

One can carry this relative reduction past merely choosing an unrelated zero for each λ. The elementary degree-continuation argument gives a connected compact subset C_b of Z_b meeting both endpoint fibers of the parameter interval. Here is the argument at the needed scope. If no connected component meets both endpoint zero sets, compactness and the equality of components and quasi-components in compact Hausdorff spaces separate Z_b into disjoint compact sets Z_b^− and Z_b^+, containing respectively all left and all right endpoint zeros. Choose a relative open neighborhood U of Z_b^− with compact closure in Ω_b and boundary disjoint from Z_b. The restricted degree on U_λ is constant in λ by the same parameter-dependent degree/excision principle used in the source. At the left endpoint it is the full nonzero degree; at the right it is zero. This contradiction supplies C_b. Its projection is a connected subset of the parameter interval containing both endpoints, hence the entire interval.

Let b tend to infinity. All C_b lie in one compact finite-dimensional parameter box. After a subsequence they converge in Hausdorff distance to a nonempty compact connected C, and its projection still covers the entire parameter interval. Compactness of closed subsets here follows, for example, by taking successive finite 2^(−j)-nets of the parameter box and a diagonal subsequence; connectedness of the limit follows because two separated closed pieces of a proposed disconnected limit would separate every sufficiently close C_b. For each point of C, choose approximating points from C_b. On every finite time interval, the source's a priori estimates and no-premature-inner-blowup argument give the same solution convergence used in its infinite-time extraction. A diagonal limit, and uniqueness from the limiting smooth initial metric, produces a flow remaining in the prescribed class for all rescaled times. The source scalar/full-curvature barrier proof then applies to each resulting flow on its fixed closed manifold up to finite maximal time.

This is a connected *set* of selected data in the prescribed parameter presentation. It is not automatically a graph λ↦c(λ), much less a smooth graph. Nor does the fixed-coefficient volume argument prove pairwise geometric inequivalence after the shooting coefficients are allowed to vary; that extra assertion has not been made. The admissible perturbation and set-valued continuation already use the complete compatible paid construction. They are not evidence of a new stability operation. The remaining smooth-selector/relative-stability question must survive this stronger reduction, rather than being justified by the failure of a naive finite-time estimate.

## 7. What a nonroutine parametric construction would actually have to do

The next candidate mechanism is not a changed exponent, a product, or a sharp-cap limit. It is a relative construction of the singular flows when genuine transverse geometric data vary, with all cap/core matching and the same scalar barrier. No theorem at that scope has been frozen: feasibility at full scope has not been established.

The triangular linearization already shows why ordinary finite-time dependence is inadequate. In the rescaled sideways coordinate γ=r/sqrt(δ), write U=log(φ/sqrt(δ)) and Z=r_s². At the Ricci-flat cone,

    U₀=log((A/B)γ),    Z₀=B².

The U equation is

    U_τ = Z U_γγ + ((Z+q−1)/γ−γ/2)U_γ
          −(p−1)e^(−2U)+1/2.

Its linearization w=U−U₀ has no first-order Z forcing, since U₀''+U₀'/γ=0. Thus

    w_τ = L_U w,
    L_U=B²[∂_γγ +(m/γ−γ/(2B²))∂_γ +2(m−1)/γ²].

The indicial equation b²+(m−1)b+2(m−1)=0 has b=−d as the chosen root. Set x=γ²/(4B²) and w=γ^(−d)P(x). Direct differentiation gives

    L_U(γ^(−d)P)
      = γ^(−d)[xP''+((m+1−2d)/2−x)P'+(d/2)P].

Consequently the generalized Laguerre polynomial of degree j, with parameter α=(m−1−2d)/2, gives an exact eigenfunction with growth exponent

    ρ_j=d/2−j.

For the selected k-mode the desired rate is exp(−ντ), ν=k−d/2. A nonzero lower-mode perturbation j<k therefore grows relative to this target as exp((k−j)τ). This is an exact linear statement, not a proof of nonlinear instability of the closed flow or of the absence of some specially tuned nonlinear family.

A full nonlinear projection, including moving-cutoff and gauge terms, would have the form

    a_j'=ρ_j a_j+N_j,      b_j=e^(ντ)a_j,
    b_j'=(k−j)b_j+e^(ντ)N_j.

For a bounded relative coefficient b_j, variation of constants forces the terminal selection equation

    b_j(τ) = −∫_τ^∞ exp(−(k−j)(s−τ)) exp(νs)N_j(s) ds.

In particular ||b_j||_∞≤(k−j)^(−1)||exp(ν·)N_j||_∞, whenever the right side is defined. This is the actual candidate graph equation, not a vague appeal to stability. A contraction argument would require a closed infinite-time solution operator and a bound on the difference of these projected nonlinear forcings in a norm that simultaneously controls the cap, neck, parabolic region, outer region, and every derivative entering the scalar barrier. Moving inner cutoff γ≈exp(−ντ/d) creates boundary/projection terms that must be included in N_j. The original weighted inequalities do not set them to zero.

The strongest existing alternative to a naive contraction is the primary topological degree construction. It tunes finitely many lower U and Z coefficients, proves that zeros stay inside the admissible box, preserves a nonzero degree, and extracts a zero for arbitrarily long time intervals. This already constructs the desired isolated flows. A nonzero degree does not make that zero unique or give an invertible derivative with respect to the shooting coefficients. It therefore does not, without further work, give a smooth global selector or the above relative graph under a new geometric perturbation.

Nor can the tree companion's analytic path-selection theorem simply replace the missing argument. That theorem operates on its explicitly proved quadratic-sector holomorphic multivariable expansion class, with recursive coefficient control, polynomial logarithmic terms at positive exponents, a common ordinary analytic parameter domain, and uniform remainders. Its geometric application is the finite-dimensional elliptic Ricci-flat-tree family. No proof has identified the infinite-time parabolic shooting map, moving boundary terms, or its zeros with that class. The connected zero-set construction in section6a already captures the topological continuation available without such an identification. Selecting a contradiction curve in the elliptic parameter space is not a global smooth selector for closed singular flows.

The unpaid obligation is therefore concrete: construct and estimate the infinite-time parabolic solution/selection operator in a compatible space, including all lower U/Z modes and cap/core matching, and prove persistence of the supplied positivity, monotonicity, reaction and scalar-barrier margins. Neither an open set of initial metrics nor a nontrivial smooth selected family satisfying those conditions is established here; section6a records the stronger paid set-valued continuation that is available. The fact that a crude Gronwall estimate diverges is not evidence of novelty; the degree construction and the terminal graph equation above are the stronger alternatives actually considered.

### 7a. Coupled equations and the strongest paid coefficient control

A further primary read was made after the first draft of sections 1–8: the complete operative coefficient-estimate file, excluding one inactive commented line, and the inner barrier proof. This is a late comparison, before any freeze. It strengthens the paid reduction and narrows the remaining obligation; it is not represented as an earlier read.

Set ζ=Z−B². Directly linearizing the full Z equation gives

    ζ_τ = L_Z ζ − 4p B^4 w_γ/γ + Q_Z,
    L_Z=B²[∂_γγ+((m−2)/γ−γ/(2B²))∂_γ−2(m−1)/γ²].

The exact nonlinear remainder in the U equation is

    Q_U = ζ(w_γγ+w_γ/γ)
          −(q−1)γ^(−2)(exp(−2w)−1+2w).

The exact remainder in the Z equation is

    Q_Z = ζ ζ_γγ − (ζ_γ)²/2 − ζ ζ_γ/γ
          −2(m−1)ζ²/γ² −8pB² ζ w_γ/γ
          −4pζ² w_γ/γ −2p(B²+ζ)²(w_γ)².

Thus the U block is triangular to first order, but the Z block is genuinely forced by U. A separate scalar shooting equation for U alone would not preserve the full construction.

For ζ=γ²Q(x), x=γ²/(4B²), direct substitution yields

    L_Z(γ²Q)=γ²[xQ''+((m+3)/2−x)Q'−Q].

The polynomial modes have growth rates −1−j. Relative to exp(−ντ), the lower Z modes grow at ν−1−j whenever j+1<ν. Since d/2∈(1,5/4), the U rates d/2−i and the Z rates −1−j do not coincide. This removes an exact finite-dimensional spectral resonance in the triangular linear system; it does not construct a nonlinear family. Gauge equivalences have not been used to claim any dimension of physical moduli.

The primary CoeffEst.tex proof is stronger than a raw mode-counting obstruction. It controls the nonlinear forcing in Gaussian weighted H^(−1) spaces for the U and Z blocks. For one solution remaining in the admissible class, its actual conclusion (with source constants and some ε>0) is

    ||Q_U and U cutoff terms||_(H^−1_m) ≤ C exp(−(ν+ε)τ),
    ||Q_Z and Z cutoff terms||_(H^−1_(m−2)) ≤ C exp(−(ν+ε)τ),
    ||U-to-Z forcing after subtracting the k profile||_(H^−1_(m−2))
           ≤ C exp(−ντ)(exp(−ετ)+η¹_U).

These statements include inner, parabolic and outer contributions, not only one path or one annulus. The inner integration gains a power of the shrinking radial cutoff. The outer Gaussian weight makes polynomially bounded errors beyond M exp(βτ) doubly exponentially small. The source proves the initial projection errors by the same inner/outer split, then pairs the Duhamel formulas with the finitely many lower eigenfunctions using H^1/H^(−1) duality. With vanishing final lower projections it obtains

    |p_shoot| ≤ C exp(−ντ₀)exp(−ετ₀),
    |q_shoot| ≤ C exp(−ντ₀)(exp(−ετ₀)+η¹_U).

These are precisely the paid quantitative coefficient estimates used to keep zeros away from the shooting boundary in the degree argument. The terminal equation in section 7 is their infinite-time variation-of-constants analogue, not a newly invented selection principle.

For additional concrete bookkeeping, let γ_b=Y exp(−ντ/d), and consider a smooth inner cutoff supported on [γ_b,2γ_b]. If w and its scale derivatives are O(1) there, the pairing of its spatial commutator with a fixed lower U eigenfunction O(γ^(−d)), against γ^m exp(−γ²/(4B²))dγ, is bounded by Cγ_b^(m−d−1). After multiplication by exp(ντ), this is

    C_Y exp(−ν(m−2d−1)τ/d),

which decays for the supplied sufficiently high dimensions. The time-cutoff contribution has two fewer inverse radial powers and decays faster. On [γ_b,1], the quadratic forcing estimate O(exp(−2ντ)γ^(−2d−2)) has projection bounded by C exp(−2ντ) when m>3d+1, which holds for sufficiently large q. These direct computations explain why treating the inner cutoff as an uncontrolled term would understate the paid construction. They are compatible with, and weaker than, the source's full weighted estimates.

What is still missing is a *difference* estimate in a complete infinite-time space for actual solutions and varying admissible geometric data, together with the existence of a solution map on that space. Bounds for individual solutions conditioned on remaining in the box do not establish such a map. The H^(−1) coefficient controls do not independently control all pointwise derivatives, inner sign conditions and nonlinear matching needed to keep a perturbed trajectory in that box. A valid contraction, implicit-function, or relative-degree construction must address that circular dependence. No such construction has been proved in this round.

## 8. Why the four-dimensional and elliptic companions do not supply that bridge

The four-dimensional result is same-manifold smooth extension of any closed real four-dimensional flow with a uniform scalar bound. Its proof already constructs the finite Ricci-flat tree, all necks, nontrivial end quotient groups, buffered times, parabolic Ricci improvement, collar fillings and renormalized variational contradiction. Repeating that reduction after adding compactness hypotheses would be a paid composition. The theorem does not provide an effective bound uniform over an unspecified class of initial metrics.

The tree theorem fixes finite combinatorics and the vertex geometries, uses diverging lengths and root decay q_root>1, and concludes E=o(M) for its scale-neutral weighted Ricci error. Its proof already establishes finite augmented inverses, critical seam matching, uniform small analytic families, all-order tails, weighted length derivatives and the finite-variation selected-path contradiction. In the flow application an arbitrary-patch extraction argument already turns the sequential assertion into the uniform small factor needed on all selected time patches.

The fixed-ALE Lojasiewicz reduction read in Deruelle–Ozuch uses a Fredholm gradient linearization on one ALE background and an analytic finite-dimensional kernel reduction. Its proof gives a power after reducing to an analytic finite-dimensional germ. That does not make the tree compactification analytic in exp(−L) across all ends: the source class permits logarithmic polynomial terms and multivariable asymptotic scales. No uniform Fredholm inverse, common power exponent, or analytic realization on a growing tree has been established in these notes. The stronger source argument, rather than a bare citation to ordinary Lojasiewicz, is already the paid operation at the supplied degenerating scope.

These comparisons were completed before any proposed theorem was frozen. The present outcome remains PREFREEZE / no nominee. The concrete global measure propagation, concentration calculations, parameter-compatibility check, and projected terminal equations are retained so the round is not merely a named gap.

## 9. Late integral-continuation comparison

After the concentration derivation, the complete critical-Rm extension proof in Bing Wang, arXiv:0704.3018v2, section3 was read. It chooses a maximal-curvature blowup, obtains a smooth noncollapsed ancient limit, and uses absolute continuity of the finite scale-invariant spacetime integral to force the normalized limit to be flat. For the present flow, section4 instead gives divergence at p=(n+2)/2, since its exact threshold is p_*<(n+2)/2. Thus that complete classical reduction is compatible with the derived concentration law and yields no continuation. Its noncollapse and smooth-limit inputs arise in a full-curvature-normalized blowup; they are not inferred from the scalar bound alone. The separate Ricci-lower-bound/scalar-integral theorem was not used as an established proof input here.
