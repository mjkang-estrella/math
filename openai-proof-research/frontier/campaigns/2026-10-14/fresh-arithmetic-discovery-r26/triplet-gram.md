# Exact triplet replacement for the completeness identity

This is technical support for T266, not its proof. The frozen unrestricted target remains unchanged.

Fix a triplet (I,H/√6,K/√6). Let D={e_i−e_j:i≠j}, a set of30 charges. For any unscaled Hadamard L, define the30×6 matrix V_L with (d,k) entry equal to the monomial L_{·k}^d, and let S_L=V_L V_L*. Equivalently, (S_L)_{d,e}=6g_L(d−e).

Direct column orthogonality gives

    V_L* V_L=36I_6−6J_6,  V_L 1=0.

Indeed, its (k,l) entry is |Σ_i conjugate(L_ik)L_il|²−6, equal to30 if k=l and −6 otherwise. Thus S_L²=36S_L and tr(S_L)=180. Consequently P_L=S_L/36 is an orthogonal projection of rank5.

Mutual unbiasedness of H/√6 and K/√6 gives V_H*V_K=0: each entry is |Σ_i conjugate(H_ik)K_il|²−6=0. Therefore P_H P_K=0. The genuine replacement for the source's complete-set resolution of the identity is

    R=I_30−P_H−P_K,
    R*=R, R²=R, R≥0, tr(R)=rank(R)=20.

The rank follows because the two rank5 ranges are orthogonal. This proves all displayed assertions for every triplet without a parametrized family assumption. It also makes the rank constraints dependent on the original equations: R²=R and tr(R)=20, hence the rank and all21×21 minors, are already consequences of Hadamard orthogonality and unbiasedness. Introducing R does not manufacture an additional vanishing equation.

For a complete set of seven bases there are six external matrices, whose six orthogonal rank5 ranges fill this30-dimensional space. Then R=0. Off-diagonal entries recover the source's order-two sum rule. For a triplet R is never zero. Its positivity may be used in a new certificate, but setting its off-diagonal entries to zero is unjustified.

## An exact triplet refutes direct reuse of the order-two sum rule

Use the explicit source tensor-product triplet. Write ω=e^(2πi/3), F_jk=ω^(jk) for0≤j,k≤2, D0=diag(1,ω,ω),

    H=[[1,1],[1,−1]]⊗F,
    K=[[1,1],[i,−i]]⊗D0F.

Both are unscaled Hadamards and |(H*K)_ij|²=6. These facts follow by multiplying the2×2 factors and the three-term quadratic Gauss sums, as in the source's lower-bound lemma. In row order(0,0),(0,1),(0,2),(1,0),(1,1),(1,2), set a=(−2,0,0,0,1,1). Then g_H(a)=1 and g_K(a)=−ω²=1+ω. Thus

    g_H(a)+g_K(a)=2+ω ≠0.

For H the column monomial is1. For K, the two entries in rows4,5 contribute i²ω^(1²+2²)ω^((1+2)k)=−ω², independently of the column; the reference row0 is1. The nonzero result follows from Im(ω)>0. This is an actual MUB triplet, not an abstract moment countermodel. It refutes only transplanting the seven-basis sum rule to two external bases, not T266.

In the source's shared-column functions, replacing the average over five other external bases by the sole other matrix also changes the Gram formula: the (1,1) entry is simply M((1,1,0);a,−v,v−a), with coefficient1. There is no distinct-label contribution of coefficient4/5 because a reference basis in a triplet has only two external bases. More importantly, the singleton order-two reduction disappears entirely; the displayed exact example prevents replacing its denominator7−l by3−l while keeping a zero total sum.

The same-matrix contraction and different-matrix cross identity remain valid for triplets. They were proved in the source without completeness. They do not by themselves supply the printed mixed certificate, which uses the missing singleton reduction.

## The third-charge polynomial lies outside the existing finite table

For one orientation write α_I=+1 on a three-subset I and −1 on its complement. The target product Γ_H(3α)Γ_H*(3α) is a positive-normalized sum over I,J and four independently sampled column/row indices. Its Laurent expansion in the36 entries of H has positive coefficients before collecting equal monomials. Its maximum exponent-matrix order (sum of positive entries) is36.

An explicit order36 monomial is obtained as follows. Choose I containing row2 and not row3, with charge a=3α_I. Choose J containing column1 and not column0, with charge b=3α_J. In |g_H(a)|² take column0 for the positive factor and column1 for the negative one. In |g_H*(b)|² take row2 for the first factor and row3 for its conjugate. The exponent matrix is

    A_i0 += a_i, A_i1 −= a_i;
    A_2j −= b_j, A_3j += b_j.

Each of the two contributions has order18. At their four intersections their signs agree by construction, so there is no cancellation; their sum has order36. The coefficient is positive, and no collected coefficient can cancel it. All row and column sums are zero.

The source's actual pair/mixed tables have total charge order at most11, and the printed pair objective has order10. Merging rows/columns and the listed symmetries cannot increase exponent order. Consequently the existing finite linear substitution table, used without multiplying relations by further monomials, cannot directly reduce this order36 objective. New higher-order relations or a lower-order factorization with new positive implications are needed. This is a limitation of those exact printed tables, not a lower bound on all possible certificates and not a proof that the target is false.

## Current unpaid step

The proposed replacement retains R correctly, but its projection/rank properties follow from the old triplet equations and have not yielded a positive identity for the third-charge product. No rational positive Gram matrix, ideal-membership certificate, cube classification, or scalar inequality forcing that product to zero has been obtained. The first-charge theorem and no-quadruplet theorem cannot be substituted for this missing orientation-coupled relation.
