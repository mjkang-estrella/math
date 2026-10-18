# Uniform fractional short-cutoff square bound for affine slopes

Fix 0<α<1, a>0 and real κ,β,b with |β|a≤1/4. No bound on κ or b is needed for this supporting estimate. Let u(x,y)=κx+βy+b and V_t f(x,y)=f(x−t,y−tu(x,y)). Put δ_k=a2^(−k−1), k≥0, and

    A_k(s)f=∫_1^s [V_(δ_k r)f−V_(−δ_k r)f]dr/r,  1≤s≤2.

Then the author derivation below proves

    Σ_(k≥0) ∫_(R²) ||A_k(·)f(z)||_(W^{α,2}[1,2])² dz ≤ C_α||f||₂².    (AF)

Use the Gagliardo norm defined in r67. In particular α∈(1/2,1) controls the square sum of within-annulus maxima. This is not the full maximal target: affine slopes are a special class, can be unbounded globally, and (AF) controls only the short part of the truncation decomposition. Local restrictions to strips where the slope is bounded fit the source interface, but are not substituted for general fields.

## 1. Exact conjugation, including transverse slope dependence

If β≠0 set c=κ/β, d=(b+c)/β and q=y+cx+d. This affine shear has Jacobian one. Direct substitution gives

    F_t:(x,q)↦(x−t,(1−βt)q).

Indeed the coefficient of tx is βc−κ=0 and the remaining t coefficient is βd−b−c=0. Because 1−βt>0 for |t|≤a, the half-planes q>0 and q<0 are preserved. The line q=0 has zero measure.

On either half-plane set q=σ exp(r), σ∈{−1,1}. The map

    (Uf)_σ(x,r)=exp(r/2) f(x,σ exp(r)−cx−d)

is unitary from L²(dxdy) to the direct sum of two L²(dxdr) spaces. Under it,

    U V_t U^(−1)g(x,r)=(1−βt)^(−1/2)g(x−t,r+log(1−βt)).

The factor is essential; simply composing with log|q| would not preserve L². Fourier transformation in (x,r) yields the multiplier

    m_t(ξ,η)=(1−βt)^(−1/2) exp(−iξt+iηlog(1−βt)).

For β=0 use instead Q=y−κx²/2−bx. This nonlinear shear also preserves area, and the exact frozen map becomes

    (x,Q)↦(x−t,Q−κt²/2).

The corresponding Fourier multiplier is exp(−iξt−iκηt²/2). The argument below treats the two cases with the same scalar estimates. These changes of variables are exact for finite t, not Taylor approximations.

## 2. Scalar phase estimates when β≠0

Set λ=ξ+βη, μ=ηβ², τ=βδ for one scale δ=δ_k. For sign σ the phase of m_(σδr) is

    φ_σ(r)=−σλδr+η[log(1−στr)+στr],
    φ'_σ(r)=−σλδ−μδ² r/(1−στr),
    φ''_σ(r)=−μδ²/(1−στr)².

The scalar primitive multiplier is

    a_k(s)=Σ_(σ=±1) σ ∫_1^s h_σ(r)exp(iφ_σ(r))dr,
    h_σ(r)=(1−στr)^(−1/2)/r.

Since |τr|≤1/4 on [1,2], h_σ and its first derivative are bounded absolutely. Put L_k=max(|λ|δ_k,|μ|δ_k²).

Low scales L_k≤1: |φ_σ(r)|≤C L_k by the Taylor remainder bound |log(1−z)+z|≤Cz² for |z|≤1/4. Also |h_+(r)−h_−(r)|≤C|τ|. Subtract the two integrands, using |exp(iφ)−1|≤|φ|, to obtain

    sup_s |a_k(s)|+sup_s |a'_k(s)| ≤ C(L_k+|β|δ_k).

Thus ||a_k||_W²≤C_α(L_k²+β²δ_k²).

High scales L_k>1: call a scale exceptional if both quantities are nonzero and

    1/8 < |λ|/(|μ|δ_k) < 8.

There are at most seven exceptional dyadic scales, since this ratio doubles when k increases by one. At these scales the elementary bounds |a_k|+|a'_k|≤C give ||a_k||_W²≤C_α. No stationary-phase estimate is required.

At every other high scale, either |λ|δ≥8|μ|δ² or the reverse. Since 4/5≤r/(1−στr)≤8/3, both phases satisfy |φ'_σ|≥c L_k, while |φ''_σ|≤C L_k. Integration by parts on any interval [1,s] gives

    sup_s |a_k(s)|≤C/L_k,    sup_s |a'_k(s)|≤C.

For example, the boundary terms h/(iφ') are O(1/L_k), and the integral of |h'|/|φ'|+|h φ''|/|φ'|² is also O(1/L_k). This argument is uniform in the possibly large frequencies and affine coefficients.

It follows that |a_k(s)−a_k(r)|≤C min(|s−r|,L_k^(−1)). Split the Gagliardo integral at |s−r|=L_k^(−1), exactly as in r67, obtaining

    ||a_k||_W²≤C_α L_k^(2α−2).

## 3. Summation and the β=0 case

For nonzero (λ,μ), L_(k+1) lies between L_k/4 and L_k/2. Hence the sum of L_k² over L_k≤1 and the sum of L_k^(2α−2) over L_k>1 are bounded by constants depending only on α. The at most seven exceptional scales contribute another C_α. The amplitude term sums to β²Σδ_k²=β²a²/3≤1/48. If λ=μ=0, all phases vanish and only this amplitude estimate is needed. Thus

    sup_(ξ,η) Σ_k ||a_k(ξ,η;·)||_W² ≤ C_α.

When β=0, replace λ by ξ, μ by κη, and φ_σ by −σλδr−μδ²r²/2; h_σ=1/r. The same low/high/exceptional classification and estimates apply, now without the amplitude term βδ. This includes κ=0.

Apply Tonelli and Plancherel separately to the endpoint L² term and the double-difference term. The coordinate maps are unitary and independent of k,s, so their changes of measure also commute with this nonnegative integration. This proves (AF), initially on a dense class supported away from q=0 in the β≠0 coordinates and then on L² by completion. Fixed-time composition is uniformly bounded because |1−βt|≥3/4. For Schwartz inputs the resulting operators agree with the defining integrals; no pointwise definition on the null line is needed.

All constants are independent of κ,β,b,a subject to |β|a≤1/4. The proof is a complete supporting calculation, not an inference from scalar pointwise symbol bounds for general variable fields.
