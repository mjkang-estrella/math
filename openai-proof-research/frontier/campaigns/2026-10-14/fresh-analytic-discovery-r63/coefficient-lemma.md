# A surviving selected main-coefficient estimate

This is an author-level technical deduction from stipulated source083, not a full maximal theorem. Use precisely the finite reference-line setting of05-concentration.tex, with fixed reference slope t, transverse width W, d_s=w/ℓ_s, bounded label/lattice multiplicity, and common finite-dimensional Hilbert space H. Let Q be a t-box. Restrict to source tiles centered in Q with ℓ_s≤length(Q), and let ||g(z)||_H≤1. Let ε:R²→[0,∞] be ANY measurable function. Define

    a^ε_s,j = |R_s|⁻¹ ∫ 1_{ε(z)<ℓ_s} 1_{|u(z)−t|≤w/ℓ_s}
                       g_j(z) overline{b_s,j(t) Ψ_s,j(z)} dz.

Then, with the same fixed packet constants,

    Σ_s ||a^ε_s||_H² |R_s| ≤ C |Q|,                              (C)

uniformly in ε, number of scales, and dim H. Deleting any fixed subcollection preserves the conclusion. This does not quantify over new nonsmooth synthesizing packets.

Proof. Dualize the left square root against vectors c_s with Σ_s||c_s||²|R_s|=1. After moving the finite sum inside the integral and using ||g||≤1, the pairing is at most the L¹ norm of

    Σ_s 1_{ε(z)<ℓ_s≤w/|u(z)−t|}
             (c_s,j b_s,j(t) Ψ_s,j(z))_j .

Use upper endpoint∞ when u(z)=t. At every z the selected lengths form one interval, possibly empty. Therefore its norm is pointwise bounded by the maximal interval-length synthesis of the fixed packets. The b_s,j(t) factors are bounded and nonzero only in the source separated reference-line frequency annuli, so they can be absorbed into c_s as in tile:lem-synthesis. The proof of conc:coefficient-carleson applies that separated synthesis estimate with a polynomial weight P_Q centered at Q, satisfying ∫P_Q⁻²≤C|Q|. It gives

    ∫ ||selected sum|| ≤ (∫P_Q⁻²)^(1/2)
                         ||P_Q maximal-interval synthesis||₂
                      ≤ C|Q|^(1/2).

Take the supremum over c_s and square to prove(C). No adaptation or regularity of ε was used; it only selected an interval at evaluation. The source weighted synthesis is already an interval maximum, so no new martingale stopping theorem is being asserted.

The main/error split also retains the source's pointwise single-scale positive error majorant after multiplication by1_{ε(z)<ℓ_s}: at a fixed scale this factor has absolute value≤1 and multiplies the same difference between b_s,j(u(z)) and the reference selector. Consequently the triangle/envelope upper estimate in conc:single-scale is unchanged. This observation controls that specific majorant, not all global size/density selection and phase estimates.

Credit: the polynomially weighted Hilbert-valued maximal synthesis and reference-line Carleson proof are source083,03-ordinary-tiles.tex tile:lem-synthesis and05-concentration.tex conc:coefficient-carleson. The only change above is the additional suffix indicator; its intersection with the existing prefix is an interval. This is an explicit standard-operation consequence, with no contribution or priority claim.
