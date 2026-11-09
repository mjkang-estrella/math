# Author assistance: a projection/channel formulation of the global tensor gap

This is collaborative development for the full all-dimensional source101 entropy stability target. It is not an independent review or a standalone nominee. The desired algebra statement is a dimension-independent estimate dist_F(T,O)^2≤C R(T)^2 for every fully symmetric real cubic tensor, or at least entrance into the established absolute-radius neighborhood when R is sufficiently small. No such statement is proved here.

Write X_r=(T_rij), B=Σ_r X_r², C=Σ_(r<s)||[X_r,X_s]||_F². All norms and traces are UNNORMALIZED. Work on the real Hilbert space M_m(R), with its Frobenius inner product. Define

S(A)=Σ_r <X_r,A> X_r,
K(A)=Σ_r X_r A X_r.

These are selfadjoint superoperators. K is completely positive (its complexification has the same real symmetric Kraus matrices). If B=I it is unital and trace preserving. S has range in symmetric matrices and annihilates skew-symmetric matrices.

## Exact identities, including B not equal to I

Full symmetry gives <X_r,X_s>=Σ_ij T_rij T_sij=B_rs. Let J:R^m→M_m(R) map e_r to X_r. Then J*J=B and S=JJ*. Consequently

||S||_HS²=tr(B²).

In entry coordinates, S_(ij),(kl)=Σ_r T_rij T_rkl and K_(ij),(kl)=Σ_r T_rik T_rlj. The two coefficient arrays differ only by a permutation of indices. Thus

||K||_HS²=||S||_HS²=tr(B²).

Moreover

<S,K>_HS=Σ_(r,s) tr(X_r X_s X_r X_s).

For real symmetric matrices, ||[X,Y]||_F²=2tr(X²Y²)−2tr(XYXY). Summing over unordered pairs (the diagonal contributions cancel) yields

C=tr(B²)−Σ_(r,s)tr(X_r X_s X_r X_s).

It follows EXACTLY, without B=I, that

||S−K||_HS²=2C.                                           (1)

If B=I, J is an isometry and S=P is the orthogonal projection onto the m-dimensional slice span. Hence

rank P=m,  range P⊂Sym_m,  ||P−K||_HS=√(2C).               (2)

The dimensions here are important: the subspace has dimension m in the matrix algebra on an m-dimensional space. This is the dimension of a maximal diagonal algebra. It is not a fixed-dimensional tensor reduction.

If ||B−I||_F<1, B is positive definite and J has rank m. Let P be the orthogonal range projection. The nonzero eigenvalues of S are exactly those of B; S and P have common eigenvectors on this range. Therefore

||S−P||_HS=||B−I||_F,
||K−P||_HS≤||B−I||_F+√(2C)≤√3 R(T).                     (3)

Also ||K(I)−I||_F=||B−I||_F. This avoids silently normalizing all three indices by B^(-1/2), which would change the tensor equations and require new error estimates.

## What these identities do and do not give

For B=I, K is a Frobenius contraction. One direct proof of Kadison's inequality is to set Vx=(X_1x,...,X_mx), an isometry, and write K(A)=V* diag(A,...,A)V. Then K(A)*K(A)≤K(A*A); taking traces uses trace preservation. Hence ||K||op≤1, while ||P||op=1. From (2),

||K²−K||_HS≤3||K−P||_HS.

This is approximate idempotence, not an exact conditional expectation. Taking powers does NOT generally round a nearly idempotent bistochastic CP map to a nearby fixed-point projection. For example on M_2 take K_epsilon=(1−epsilon)Id+epsilon D, where D is the diagonal pinching channel. As epsilon→0 it is arbitrarily close to the identity projection, but lim_n K_epsilon^n=D, at a fixed positive HS distance from identity. This example does not satisfy every rank/cubic symmetry constraint of (2), and is not a counterexample to the target; it only rules out that unqualified powers argument.

Likewise, a spectral projection onto eigenvalues near1 need not be completely positive. An additional dimension-uniform rounding theorem preserving the relevant algebraic positivity is required. No such theorem is claimed from the exact odeco characterization.

## Relation to the maximum-cubic calculation

For a unit vector v, full symmetry gives K(vv^T)=L_v² and S(vv^T)=L_(T(v,v)), where L_v=Σv_r X_r. At a constrained maximum T(v,v)=lambda v, the discrepancy is lambda L_v−L_v². If the tangent eigenvalues are mu_i, its squared Frobenius norm is Σ mu_i²(lambda−mu_i)². Thus the channel identity recovers the parent's eigenvalue obstruction rather than magically supplying a lower bound for lambda. Its possible benefit is simultaneous control on all matrix inputs, instead of a single maximizing vector.

The missing global step is now precise: round the rank-m selfadjoint range projection P, close in absolute HS norm to the special CP reshuffling K, to a maximal diagonal algebra with a dimension-independent estimate; then recover the compatible cubic coefficients. Arbitrary almost-commuting matrix theorems or arbitrary CP-map stability statements cannot be applied without checking this rank, norm, symmetry and positivity interface.
