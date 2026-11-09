# Transferring the enlarged-space correction back

Author continuation, conditional on the checked constructions in the two preceding r69 notes. This proves only the exact-B, small-D supporting case; it does not supply either initial reduction for T101G69.

Use Pi,W,Y,sigma as in high-space-completion.md. Let Q=Pi J:V->W. Its singular values belong to [sqrt(1−2d),1]. Choose the first m basis vectors of W by the isometry Y=Q(Q*Q)^(-1/2), and complete them to an orthonormal basis. In family HS norm,

  ||Y−J||HS<=2||(I−Pi)J||HS<=2sqrt(2C).                (1)

Indeed ||Y−Q||HS²=sum(1−s_i)²<=sum(1−s_i²)=||(I−Pi)J||HS². Here and below Y−J denotes the difference of the corresponding matrix-valued maps.

Let U_abc=tr(XaXbXc) on V. The r67 identity U−T=hA gives ||U−T||HS<=sqrt(2C). Comparing the old m-by-m-by-m block of sigma to U by three telescoping terms gives

  ||sigma_old−U||HS<=3sqrt(h0)||Y−J||HS.               (2)

To check the norm used here, a matrix family Z_i that is orthonormal in HS and has row Gram <=h0 I satisfies ||(c_ij)->sum c_ij Zi Zj||_(tensor->HS)<=sqrt(h0). Group by one index and apply row Cauchy–Schwarz; the sum of squared HS norms of the grouped orthonormal combinations is ||c||². The same proof works for the mixed X/Y families appearing in the telescoping terms. Pairing this product map with the difference family proves (2), without a dimension factor.

Since B_sigma<=h0 I, the squared norm of all sigma coefficients with at least one of the r new indices is <=3h0 r. Consequently, writing T^ext=T on V and zero on all mixed/new coordinates,

  ||sigma−T^ext||HS²<=constant*C,                     (3)

because r<=8C. Operator-density-correction.md supplies an orthodeco tensor O_W with ||sigma−O_W||HS²<=constant*C for d sufficiently small. Thus the same bound holds between T^ext and O_W.

## Compression of a unit orthodeco tensor

Let O_W=sum_(i=1)^(m+r) u_i^tensor3, with u_i an orthonormal basis of W. Put v_i=P_V u_i. The m-by-(m+r) matrix V0_all with these columns is a coisometry; its Gram is an orthogonal projection. Choose any m columns, denoting their square matrix by V0, and discard the other r. Complete a polar factor of V0 to an orthogonal matrix W0 with columns w_i. Singular values s_i<=1 give

  ||V0−W0||F²=sum_i(1−s_i)²
      <=m−||V0||F²=sum_discarded||v_i||²<=r.           (4)

This remains true for a singular V0: a full orthogonal polar completion exists and the zero singular values contribute1 on both sides of the inequality.

The norm of the discarded cubic is <=sqrt(r). Indeed its squared norm is sum_ij <v_i,v_j>³, bounded by sum_ij |<v_i,v_j>|³ <=sum_ij <v_i,v_j>² <=r because the discarded Gram is a positive contraction.

Also

  ||sum_selected v_i^tensor3−sum_i w_i^tensor3||HS
       <=3||V0−W0||F<=3sqrt(r).                       (5)

For each telescoping term, the Gram of the paired unchanged factors is a Hadamard product of contraction Grams, bounded by I. This follows directly from the Schur product theorem: if 0<=G<=I, then G circle G <= I circle G=diag G<=I; mixed orthonormal factors give G circle I=diag G. Thus each term is bounded by the Frobenius norm of the changed factor.

Combining the discarded and selected terms,

  dist(P_V^tensor3 O_W,O_V)<=4sqrt(r).                 (6)

Orthogonal compression is a contraction, so (3),(6) imply

  dist(T,O_V)²<=constant*C.                            (7)

The absolute constant is independent of m and C, but the hypothesis remains exact B=I and d=||D||op below a sufficiently small fixed threshold. This is the supporting case obtained by latent-mode completion, rather than the invalid substitution D small => S−K small.

The full frozen theorem still requires arbitrary B<=2I and arbitrary D. No reduction establishing those cases is claimed. These notes are collaborative author work, not a campaign proof/contribution verdict.
