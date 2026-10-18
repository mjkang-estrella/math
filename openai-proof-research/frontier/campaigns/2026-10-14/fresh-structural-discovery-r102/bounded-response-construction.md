# Bounded response tensor from the retained source remainder

Author deduction for the unchanged full entropy target. This is not the remaining global algebraic rounding theorem. Parent supplied retained separation and the initial derivative-response observation; all calculations below are author support, not independent review.

Let f(a)=q(a)/(1+q(a)), F(x)=f(A(x))=J(I+J)^(-1), and C_r=E[x_r F]. Thus 0<F<I. Define the finite scalar constants

 L0=sup|f'|<=1, L2=sup |f''|/(log q)'<infinity.

For L2, use f''=q''/(1+q)²-2q'^2/(1+q)³, q'=q d, and the already established q tails. The second term divided by d is 2q²d/(1+q)³, bounded and tending to0 at both tails. Smoothness handles the compact interval.

## 1. A globally bounded Gram and full symmetry defect

Vector-valued Gaussian Bessel applied to Fv for each constant v gives

 B_C=sum_r C_r² <= E(F-EF)² <= E F² <=I.               (1)

This is an operator inequality; it does not use a Frobenius bound depending on dimension.

Let H_rij=partial_r J_ij, a fully symmetric tensor. In a pointwise J eigenbasis with eigenvalues lambda_i=q(a_i), differentiation gives

 partial_r F_ij=H_rij/[(1+lambda_i)(1+lambda_j)].

All three indices are rotated together; no eigenvectors are differentiated. Consequently

 partial_r F_ij-partial_i F_rj
 =H_rij[(1+lambda_i)^(-1)-(1+lambda_r)^(-1)]/(1+lambda_j).

The function xi->(1+exp xi)^(-1) is1/4-Lipschitz. Also

 H_rij=q[a_i,a_j] Z_rij=q[a_r,a_j] Z_irj,
 0<q[a,b]<1.

Writing delta_ij=|log lambda_i-log lambda_j| and using the triangle inequality, the absolute curl entry is at most

 (delta_ij |Z_rij|+delta_rj |Z_irj|)/4.

Square, sum, and use r_ij>=1/16. This yields

 ||curl F||²<=4 C_sep.                                (2)

Gaussian integration by parts and Jensen imply

 sum_rij |(C_r)_ij-(C_i)_rj|²<=4 C_sep.

The matrices C_r are symmetric. Averaging the cubic over permutations thus gives a fully symmetric tensor S with

 ||S-C||F²<=4 C_sep.                                  (3)

The constant is loose. All derivatives are square integrable, since f is scalar1-Lipschitz in Frobenius functional calculus and A is in Gaussian H1. Gaussian cutoffs justify the displayed integrations by parts.

## 2. Exact double-Bessel commutator estimate

Since f is1/4-Lipschitz in log q,

 E sum_r ||[F,Z_r]||F²<=C_sep.

With Z_r=X_r+G_r and ||F||op<=1, it follows that

 D0:=E sum_r ||[F,X_r]||F²<=2C_sep+8||gradient Y||².   (4)

For independent standard Gaussians x,z, apply scalar functional calculus to the commutator in an A(z) eigenbasis. The scalar bound |f(a)-f(b)|<=L0|a-b| gives

 ||[F(z),F(x)]||F<=L0 ||[A(z),F(x)]||F.

For each fixed x, the independent centered linear pencil has

 E_z||[L(z),F(x)]||F²=sum_r||[X_r,F(x)]||F².

Moreover ||[Y(z),F(x)]||F<=2||Y(z)||F. Thus

 E_(x,z)||[F(z),F(x)]||F²
 <=L0²(2D0+8||Y||²).                                (5)

The coefficient at the orthonormal product Hermite function x_r z_s is exactly [C_r,C_s], with the harmless choice of overall sign. Hilbert-space Bessel in both independent variables therefore yields

 sum_rs ||[C_r,C_s]||F²<=L0²(2D0+8||Y||²).             (6)

This proof does not differentiate F(z) in x, divide by eigenvalue gaps, or insert Bop. Finite moments and ||F||op<=1 justify Fubini; (5) supplies the needed total Frobenius integrability.

The same single-variable Bessel argument gives a useful stronger interface:

 E_x sum_r ||[F(x),C_r]||F²
 <=E_(x,z)||[F(x),F(z)]||F².                          (7)

## 3. Quantitative nondegeneracy on all but O(delta) directions

Let N=E f'(A), positive definite. As for the q response, averaging the Frechet derivative of f and using L2 in the log-q coordinate gives

 e:=sum_r ||C_r-N X_r||F²
 <=32 L2² C_sep+2 L0²||gradient Y||².                 (8)

Indeed C_r=E partial_r F, the difference Df(A)[Z_r]-f'(A)Z_r has squared norm at most16 L2²C_sep, and the G_r part is controlled by L0. This is averaging BEFORE multiplying a comparison f'(A)-f'(L) by X_r.

Fix R=sqrt6 and c_R=min_{|a|<=R} f'(a)>0. Scalar functional calculus gives

 f'(A)>=c_R(I-A²/6),
 N>=c_R[I-(B+E Y²)/6],                              (9)

since E A²=B+E Y² by Gaussian chaos orthogonality. The spectral subspace B<=2 has codimension at most C Omega(B); the spectral subspace E Y²<=1 has codimension at most||Y||². Their intersection therefore has codimension O(Omega+||Y||²), and on it(9) is at least c_R/2. By min-max, N has only that many eigenvalues below c_R/2.

Similarly B has at most C Omega(B) eigenvalues below1/2. Write c=c_R/2. On the intersection of the good N subspace with the inverse image under N of the good B subspace,

 v^t NBN v >= (1/2)||Nv||² >= (c²/2)||v||².

The inverse-image condition has codimension at most the bad B rank, even without assuming N and B commute. Thus NBN has only O(Omega+||Y||²) eigenvalues below c²/2.

View (N X_r)_r and (C_r)_r as rectangular row operators. Their squared Frobenius distance is e and their row Gram matrices are NBN and B_C. The singular-value Hoffman-Wielandt inequality, or its min-max proof, implies

 #{lambda(B_C)<c²/8}
 <=C(Omega+||Y||²)+8e/c².                            (10)

Every unmatched singular value drops by at least c/(2sqrt2), whose squared cost is c²/8. Combining the retained source estimates with(1),(3),(6),(8),(10) gives a bounded matrix family with full symmetry defect O(delta), commutator energy O(delta), and only O(delta) eigenvalues of its Gram below the fixed positive threshold c²/8.

This is not the statement B_C≈alpha² I. No scalar calibration has been assumed. A regularized Gram normalization is a possible alternative; it is treated separately in response-normalization.md. Neither step rounds the resulting bounded cubic at large total residual.
