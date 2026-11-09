# Error density controls channel idempotence, but not the missing slice span

Author development for the unchanged T101G69 target. This note assumes exact B=I only to derive a supporting identity; it does not replace the frozen all-error B<=2I target. The r67 homotopy, normalization and channel notation are credited.

Write Jv=X_v, K(Y)=sum_r X_r Y X_r, S=JJ*, with the unnormalized matrix Hilbert–Schmidt inner product. At B=I, J is isometric, S is a rank-m orthogonal projection, K is a selfadjoint unital trace-preserving completely positive map, and its induced HS norm is at most1. Let V=J*KJ, D=I−V. Then D>=0 and tr D=C, with C=sum_(r<s)||[X_r,X_s]||F². These are r67 identities.

## 1. Exact multiplication-defect row and column Grams

For ordered r,s define

F_rs=sum_t T_rst X_t,       E_rs=X_rX_s−F_rs.

Full symmetry and B=I imply

sum_rs F_rs*F_rs=sum_rs F_rs F_rs*=I,
sum_rs E_rs*E_rs=sum_rs E_rs E_rs*=2D.                  (1)

Indeed the F sums equal sum_tu B_tu X_t X_u=I. The pure product sum is sum_s X_s B X_s=I (and analogously in the other order). For the cross term, full symmetry gives

sum_rs X_s X_r F_rs=sum_s X_s K(X_s)=V.

The last equality is entrywise: its ij entry is the contraction of four T tensors along the same tetrahedral index diagram as <X_i,K(X_j)>; explicitly the summand can be written

T_isk T_kal T_slm T_jam,

and V_ij has the same expression after renaming dummy indices. V is symmetric. Thus the two cross terms each equal V, proving the E*E identity. Since E_rs*=E_sr, the EE* identity follows as well.

## 2. Dimension-free induced-HS near-idempotence

The elementary matrix-map estimate

||sum_i A_i Y B_i*||F
 <= ||sum_i A_i A_i*||op^(1/2)
    ||sum_i B_i* B_i||op^(1/2) ||Y||F

uses the A row Gram and the B column Gram. In the present application both row and column Grams coincide. One direct proof is the operator Cauchy–Schwarz estimate for sum_i A_i⊗conj(B_i) on the vectorized HS space: factor it as a row operator followed by a column operator on the auxiliary direct sum. No factor depending on the number of Kraus operators occurs.

Expanding X_rX_s=F_rs+E_rs gives

K²(Y)=sum_rs (F_rs+E_rs)Y(F_rs+E_rs)*,
sum_rs F_rs Y F_rs*=K(Y).

Consequently, writing d=||D||op,

||K²−K||_(HS→HS) <= 2sqrt(2d)+2d.                       (2)

This is stronger than control restricted to range(J). In particular, if epsilon=2sqrt(2d)+2d<1/4, every real eigenvalue lambda of K satisfies |lambda(lambda−1)|<=epsilon. Since |lambda|<=1, negative eigenvalues have absolute value<=epsilon; nonnegative ones lie within2epsilon of0 or1.

## 3. Exactly what (2) does not establish

Let Pi=1_[1/2,1](K). It need not equal S. Since Pi is the closest orthogonal projection to the selfadjoint K in Frobenius norm (choose each eigenvalue0 or1),

||Pi−S||HS <= 2||K−S||HS = 2sqrt(2C),
|rank Pi−m| <= ||Pi−S||HS² <=8C.                         (3)

Also

||(I−Pi)J||op² <= 2||D||op,

because I−K>= (1/2)(I−Pi). If d<1/2, Pi J is injective, so rank Pi>=m. Thus there are at most8C extra nearly fixed matrix directions, while the original slice span embeds almost isometrically into Pi's range.

These are TRACE-PAID extra matrix directions, not removed vector directions. Their matrices may have full rank on V. Deleting their ranges in V can cost the entire ambient dimension, and adding them as new slice matrices does not automatically produce a fully symmetric associative cubic. The latter must satisfy mixed old/new and new/new products and Gram normalization. Neither step is proved here.

Even exact B=I does not license a claim that small D operator norm gives ||S−K||op small. The harmonic simplex family is an actual symmetric-cubic example of this distinction, developed separately below. The frozen global distance bound is still unresolved.
