# Explicit reviewer repairs; frozen author proof needs revision

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. These changes are proposed separately and do not alter any frozen author byte.

## R1. Coordinate versus metric norms

Candidate lines 126–131 specify Euclidean coordinate norms for D. Lines 358, 523, 552 and 569 then use bounds without the ellipticity factors needed to turn D²h into a metric operator bound or to turn dz₃⊗dz₃ into a coordinate bound. Definition (F) is therefore equivalent to the source preparation only up to changed constants, contrary to the literal “exactly” at lines 151–153. This is a constant bookkeeping defect, not an obstruction to the operation or T4.

Here are sufficient replacements, with deliberately unused slack. Enlarge CΓ if necessary so that |Γ dh|_E ≤ CΓ |dh|_E. Put

    K = 1 + Λ + Λ^(3/2) CΓ.

The stated metric class gives, for every 0<S≤1,

    |∇²h|_G ≤ Λ |D²h|_E + Λ^(3/2) CΓ |∇h|_G
             ≤ K(C+1)|∇h|_G/S.

After the gradient normalization on a parent, |∇h|≤2s. Replace C'' in candidate line 358 by 2K(C+1). Every use there only needs a fixed finite C'', so both branches of the retention argument remain valid.

For Lemma 6.1 put

    M = 4K(C_B+1)+4,     m = c_B/2,
    b = 4(2M+2+2M²/m+m),
    C_A = 8(C_B + bΛ h₂ + 1),     c_A=c_B/8.

Choose ν after these numbers and κ. In the transported-direction estimate replace the numerical old-Hessian norm at line 523 by 2K(C_B+1)s/S and allow the already unspecified O(ν), O(bν²) constants to depend on K. The C³ comparison and S≤ν estimate in the review imply J(e₂)≥m s/S by making ν sufficiently small.

On the full region the old mixed term, including the vanishing cutoff/connection remainder, has absolute value ≤M s/S. The old contribution to J(e₃) has absolute value ≤2M s/S. Since |dz₃(e₃)|≥1/2, H''=1 there, and all remaining errors tend to zero after b is fixed, one has

    J(e₃) ≥ (b/4-2M-1)s/S
           ≥ (2M²/m+m+1)s/S.

Thus, for α²+β²=1,

    J(αe₂+βe₃)
      ≥ [mα² + (2M²/m+m)β² -2M|αβ|]s/S
      ≥ (m/2)s/S ≥ (c_B/8)|∇v_A|/S.

Here the same scalar ∇²v_A(D_v,D_v) distributes correctly because α²+β²=1. No sign assumption on it was inserted. Also |dz₃|_E²≤Λ at the frozen center, and this covector is constant in x. Hence on the full region

    |D²v_A|_E ≤ (2C_B+bΛ h₂+1)s/S
               ≤ C_A |∇v_A|/S

after the smallness choices. The changed b depends only on C_B,c_B,Λ; C_A additionally depends on κ. The asserted dependence structure is preserved.

The literal omitted conversion cannot be valid for arbitrary Λ: in constant coordinates with G=diag(1,ε,ε), Γ=0, a transverse metric Hessian can be ε⁻¹ times its coordinate Hessian. A matrix [[c,K₀],[K₀,-K₀]] in an orthonormal transverse frame can have bounded coordinate norm with K₀≈C_B/ε. A Schur complement based on a bound independent of ε cannot control this matrix. This illustrates the invalid bound, rather than claiming a counterexample to the existential Lemma 6.1. The replacements above supply the missing bound.

## R2. Dependence of the radial error modulus

Candidate line 355 says ε in (5.4) depends only on Λ and the pattern. The O(μ) gradient error in lines 293–306 also uses the incoming C. Its square produces the C-dependent μ²|f'| term at line 329. The displayed error bookkeeping directly establishes

    ε = ε_(C,Λ,pattern)(μ) → 0

for each fixed preparation constant C, uniformly over the corresponding prepared parents. Allowing dependence on c too is harmless. Use this corrected quantifier at lines 350–377. The compact vanishing-coefficient proof is unchanged; its coefficients are bounded once C is fixed. The leading c_a and the core output constants remain pattern/Λ constants, since all old-C terms tend to zero as μ→0. The lemma already allows μ₀(C,c,Λ), so no conclusion of Lemma 5.1 needs weakening. Alternatively a universal slower modulus can dominate each fixed-C error after a C-dependent threshold; that extra majorization is not written in the candidate. R2 is a missing quantifier justification in the displayed argument, not a counterexample to existence of such a universal modulus.

## Downstream accounting

Fix the radial pattern and its gain first; then its output weak constants; then κ; then the corrected M,b,C_A,c_A; then μ₀ for that full input and for the seed; finally choose one reciprocal ν satisfying all finite absorptions. Neither change introduces higher metric derivatives or derivative-order dependence into ν. Put r=ν⁶ as before. Enlarged constants only decrease this one fixed ratio and possibly the resulting positive γ. The inherited third derivative is still multiplied by ν¹² and ν¹⁰ at the new scale. The mass gain is unchanged. All packet exponents, Gaussian exponents, correction exponents and diagonal budgets depend only on existence of the three envelope bounds, so all subsequent steps survive. Full source transfer is supplied in source-transfer.md.

Disposition: author proof needs revision. These are explicit elementary repairs supplied by this review, not edits to the authenticated submission. The review's PASS_FULL_T4 refers to the full frozen target proved with these stated repairs; it is not a claim that every displayed auxiliary constant in the unchanged candidate is correct, and does not grant campaign acceptance.
