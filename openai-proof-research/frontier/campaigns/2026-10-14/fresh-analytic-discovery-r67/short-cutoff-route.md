# Fractional short-cutoff route

Work first with a smooth compactly supported input, a positive finite lower endpoint, and the source local slope field u, |u|≤1, Lip(u)≤C_Lip, a C_Lip small. Put V_t f(x,y)=f(x−t,y−tu(x,y)). Uniform fixed-time L² bounds follow from the stipulated source change-of-variables interface; no integration along a curved flow is substituted.

For δ_k=a 2^(−k−1), k≥0, define

    A_k(s)f = ∫_1^s [V_(δ_k r)f−V_(−δ_k r)f] dr/r,  1≤s≤2.

Exactly H_a^(sδ_k)f=H_a^(δ_k)f−A_k(s)f. Thus, pointwise,

    sup_ε |H_a^ε f| ≤ sup_k |H_a^(δ_k)f|
                          + (Σ_k sup_[1,2]|A_k(s)f|²)^(1/2).       (1)

No directional positive averaging maximal bound has been inserted in (1).

For 1/2<α<1, use the fractional norm

    ||h||_(W^{α,2}[1,2])² = ∫_1²|h(s)|²ds
        + ∫_1²∫_1² |h(s)−h(r)|²/|s−r|^(1+2α) dr ds.

The elementary one-dimensional embedding sup|h|≤C_α||h||_W applies to the continuous representative. One direct proof writes h(s) as its interval average plus differences of averages over nested dyadic intervals containing s. Cauchy–Schwarz bounds each scale difference by its fractional energy times length^(α−1/2); the resulting geometric series converges exactly when α>1/2. Boundary intervals use the same nested intervals. Initially smooth h suffices here, and completion gives the indicated representative.

Consequently a concrete sufficient remaining short-cutoff estimate is

    Σ_k ∫_(R²) ||s↦A_k(s)f(z)||_(W^{α,2}[1,2])² dz
          ≤ C_α ||f||₂²,                                      (SSα)

uniform in u and all finite consecutive k ranges. This would control the second term in (1), without replacing the original target by a smooth truncation theorem. The long dyadic maximum in (1) remains a distinct unpaid estimate. (SSα) is NOT proved for variable u.

## Complete constant-direction calculation

For a constant vector b=(1,u), Fourier transformation in z turns A_k into multiplication by

    a(q,s)=−2i∫_1^s sin(qr) dr/r,   q=δ_k ξ·b.

For |q|≤1, both |a(q,s)| and |∂_s a(q,s)| are at most C|q|, giving ||a(q,·)||_W²≤C_α q².

For |q|≥1, integration by parts in r gives sup_s|a(q,s)|≤C/|q|; also sup_s|∂_s a|≤2. Therefore

    |a(q,s)−a(q,r)| ≤ C min(|s−r|, |q|^(−1)).

Splitting the Gagliardo integral at |s−r|=|q|^(−1) gives

    ||a(q,·)||_W² ≤ C_α |q|^(2α−2),

because ∫_0^(1/q) h^(1−2α)dh and q^(−2)∫_(1/q)^1 h^(−1−2α)dh both have this order; the L² term q^(−2) is smaller. These estimates hold for negative q by symmetry and q=0 by zero.

The q_k form a geometric progression. Hence

    Σ_(k≥0) min(|q_k|², |q_k|^(2α−2)) ≤ C_α

(with value zero when ξ·b=0). Sum the small-q tail with ratio 1/4 and the reversed large-q tail with ratio 2^(−2(1−α)). Tonelli and Plancherel, applied separately to the L² term and the double-difference term, prove (SSα) for constant b, uniformly in b. Together with the already credited classical one-dimensional maximal Hilbert theorem, this is only another proof of a paid special case.

## Why ordinary H¹ in the endpoint parameter fails

The derivative is ∂_s a(q,s)=−2i sin(qs)/s. For |q|≥4,

    ∫_1²|∂_s a(q,s)|²ds ≥ ∫_1² sin²(qs)ds
      ≥ 1/2−1/(2|q|) ≥ 3/8.

At frequency λ=|ξ·b| there are order log(aλ) scales with δ_k λ≥4. Thus the analogous H¹ square sum has multiplier at least c log(aλ). Concentrating a Schwartz Fourier transform in a small ball around a high frequency makes this a rigorous unboundedness example on R². Plane waves themselves are not asserted to be L² inputs. This disproves only the H¹ square-estimate shortcut, not (SSα) or the maximal target.

## Variable-field obstruction is an actual missing estimate

For variable u the pointwise symbol is a(δ_k(ξ_x+u(z)ξ_y),s), but Plancherel cannot be applied with a z-dependent multiplier. The scalar geometric sum bound does not imply an L² pseudodifferential bound. In particular, the source only permits a fixed finite list of packet seminorm bounds; differentiating or expanding in endpoint s cannot be asserted to preserve those bounds uniformly over endpoint frequency. The fractional proof needs a vector-valued oscillatory estimate with cancellation in z. No such estimate is supplied by the scalar calculation.

This route makes the sharp-cutoff obligation quantitative and identifies the useful parameter range 1/2<α<1. It does not close the selected diagonal estimate, global B1 error summation, or B2.
