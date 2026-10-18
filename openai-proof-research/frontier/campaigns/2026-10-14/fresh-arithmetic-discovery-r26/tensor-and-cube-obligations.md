# Why the remaining source operations do not close T266

These are precise boundaries of the attempted proof, not an impossibility theorem and not another target.

## Tensorizing the surviving Gram orthogonality

Use the 30-dimensional vectors v_k of triplet-gram.md. Their inner products are 30 on the diagonal and −6 off the diagonal. For every positive integer r define t_r(H)=Σ_k v_k^(⊗r). Then

    ||t_r(H)||²=6·30^r+30·(−6)^r.

If H,K are mutually unbiased transitions from the same reference basis, every inner product between a column vector for H and one for K is zero. Hence t_r(H) and t_r(K) are orthogonal. Moreover t_r(H) belongs to the range of P_H^(⊗r), and those tensor projection ranges are orthogonal. All assertions follow by expanding the finite sums and tensor inner products; no completeness assumption enters.

For a three-subset I match its three indices bijectively to its complement, obtaining d_1,d_2,d_3∈D with d_1+d_2+d_3=α_I. The coordinate of t_9(H) indexed by (d_1,d_1,d_1,d_2,d_2,d_2,d_3,d_3,d_3) equals 6g_H(3α_I). Thus this tensor lift genuinely contains the unpaid characters; it is not merely a degree-two proxy.

Nevertheless the tensor lift supplies orthogonality of whole vectors/ranges, not vanishing of these particular coordinates, nor a choice between all coordinates of H and those of H*. Its norm is positive already for r=3 and r=9. The complement of the two ranges remains present. Bessel inequalities bound coordinate mass; they do not give a zero upper bound. No identity saturating such a bound at the required coordinates was found. The exact missing operation is an intertwiner or positive certificate forcing M(H)1 or M(H)^T1 to vanish from the full triplet constraints. The projection identities alone are consequences of the original constraints and add no new independent equation.

## Hadamard-cube products do not preserve the needed hypothesis

Put L=H*K/√6 for the third transition and C_ijk=H_ij L_jk conjugate(K_ik). Each entry has modulus one. Summing over any one index gives √6, and each slice is equivalent by diagonal unitary factors to one of H,K,L or an adjoint. These are the actual cube operations in the primary triplet paper; they re-express the same triplet and supply first-charge vanishing on its slices.

A tempting step would multiply three parallel slices and reapply the pinned single-Hadamard Fourier theorem to reach third charges. Parallel slices differ only by row and column phase factors, so their entrywise product is equivalent to the entrywise cube of that transition. Entrywise cubing does not preserve Hadamard orthogonality. In the exact tensor-product triplet used in diagnostics.py, H=F_2⊗F_3 and H^(∘3)=F_2⊗J_3 has rank 2, so it is not Hadamard. Thus the required hypothesis fails inside an actual triplet, not just in a generic relaxation. This blocks this specific shortcut, not the full conjecture.

## A finite exact certificate interface remains unpaid

Write each entry of H and K as a real part plus i times a real part, giving 144 real variables. The equations are entry moduli equal to one, H*H=K*K=6I, and |(H*K)_ij|²=6. The first two classes have degree two; the unbiasedness equations have degree four. Real and imaginary parts are separated. On this domain conjugation equals inversion entrywise.

Let A_I(H)=Σ_k product_{i∈I} H_ik³ product_{i∉I} conjugate(H_ik)³ and define

    F(H)=(Σ_{|I|=3}|A_I(H)|²)(Σ_{|J|=3}|A_J(H*)|²).

This is a nonnegative real polynomial of degree 72, and F(H)=720² Γ_H(3α)Γ_H*(3α). Together with the credited first-charge input, the unchanged target is exactly F(H)=0 for every real solution of the triplet equations. A concrete sufficient exact proof interface would be an identity

    −F(H)^(2r)=Σ_l s_l(H,K)²+Σ_j p_j(H,K)e_j(H,K)

for an explicitly given positive integer r, polynomials s_l,p_j, and the explicit constraint polynomials e_j. Evaluating it on a triplet would force F=0. No such identity, degree bound, coefficient list, or complete elimination has been produced. Rational coefficients are a desirable checkable format, not an asserted existence result here. The lower-degree source certificate does not supply this identity unchanged.

The real 10×10 formulation and exact examples reduce ambiguity about the unpaid step. They neither settle T266 nor establish statistical hardness, algebraic nonexistence of certificates, or a classification of triplets.
