# Thin-strip obstruction to direct Dorronsoro transfer

Actual primary interface: Orponen, arXiv:1811.01702v2, Theorem1.1 defines normalized affine β_p coefficients and states their squared dyadic Carleson estimate for Lipschitz functions. For dimension two it permits finite p, not p=∞. Use only the normalized 1-Lipschitz case here, avoiding any issue about the displayed dependence on a general Lipschitz constant. Read the introduction through §2.2 and the planar §2.4.1 proof. The original Dorronsoro1985 body was not read.

The following disproves the direct local operator estimate with coefficient C_p β_p(Q), at the critical vertical frequency Rδ²=1, for every fixed finite p≥1. It includes the within-annulus primitive, not just a fixed-time composition.

Choose an even nonnegative C∞ bump χ supported in [−1,1], equal to a positive constant c0 near zero and with ||χ'||∞≤1. Let h→0, δ=h³ and

    u_h(x,y)=hδ χ(y/(hδ)),     Q=[−δ,δ]².

This is globally 1-Lipschitz and bounded. Against the affine competitor zero,

    β_p(Q)≤C_p h^(1+1/p).

For p>1 the unique best affine Lp approximant on the symmetric square is a constant c_h: average it under the x and y reflections and use strict convexity. For p=1 a symmetric constant minimizer can be chosen, and zero is a median because the support occupies less than half the square. The competitor-zero bound gives |c_h|≤C_p h^(1+1/p)δ from the region where u_h=0. Hence c_h=o(hδ). The affine minimizer is therefore small compared with the plateau height, for each fixed p. Diameter versus side-length normalizations change only constants.

Take a real Schwartz band-limited φ with Fourier support in [−1,1] and φ positive on a fixed neighborhood of zero (for example the inverse Fourier transform of a nonnegative even smooth bump with positive integral). Take ψ smooth compactly supported, equal to1 on [−4,4]. Put

    f_h(x,y)=ψ(x/δ) φ(y/(hδ)) exp(i R y),    R=δ^(−2).

Its vertical Fourier support is [R−1/(hδ),R+1/(hδ)]⊂[R/2,2R] for small h, because δ/h=h². Its L² norm is C sqrt(h)δ. It is Schwartz; a plane wave is not being used as an L² input.

For outputs |x|≤δ, |y|≤c hδ in the plateau and s∈[3/2,2], both horizontal shifts x±δr lie where ψ=1. The vertical envelope changes by at most Cδ under the shifts ±δr u_h, uniformly in r∈[1,2]; for the constant c_h it changes even less. The carrier phases are ±r u_h/δ and ±r c_h/δ. Pairing positive and negative times gives

    A_δ^{u_h}(s)f_h − A_δ^{c_h}(s)f_h
      = −2i exp(iRy) φ(y/(hδ))
           ∫_1^s [sin(r u_h/δ)−sin(r c_h/δ)] dr/r + O(δ).

The O(δ) envelope error is absolute, uniform on this output set; δ=h³=o(h). On the plateau u_h/δ=c0h while c_h/δ=o(h), so the integral has magnitude at least c h uniformly for s∈[3/2,2] and small h. Thus the output modulus is ≥c h on a set of area comparable to hδ². Integrating also over that s interval yields

    ||1_Q(A_δ^{u_h}−A_δ^{c_h})f_h||_(L²_z L²_s)
          ≥c h||f_h||₂.

The W^{α,2}_s norm is larger, as is the norm with sup_s. Since β_p(Q)≤C_p h^(1+1/p), their ratio to β_p(Q)||f_h||₂ tends to infinity like at least h^(−1/p). Therefore a universal local error bound C_p β_p(Q)||f||₂ is false for every finite p, even with actual best affine approximation and exact vertical band localization at parabolic frequency.

This rules out the direct local estimate which one might then try to sum by Dorronsoro's Carleson bound. It does not prove that no adaptive, anisotropic, weighted, or stopping-time transfer can work. A bound involving β∞ is compatible with this example, but the read planar theorem does not provide the corresponding β∞ squared Carleson estimate. Upgrading finite-p errors to supremum errors loses a power, and their squared Carleson sum cannot simply be reused. No universal impossibility claim for every refinement is made.
