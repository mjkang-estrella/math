# A general paid positive mixed-energy bound

Author support for the original all-deficit scope, not a nomination or completed removal theorem. This uses positivity of the actual source Jacobian and retains all noncommuting blocks.

Let L=sum_r x_r X_r with symmetric slices, B=sum_r X_r², K=q(L), and J=q(A)>0 the actual Brenier Jacobian. Write epsilon²=E||J-K||F²<=E||Y||F². Let

 Q=1_{[0,1/2) union (2,infinity)}(B), P=I-Q, k=rank Q.

The endpoint convention is immaterial; with this convention P includes both1/2 and2. Define

 c_omega=sup_{lambda outside[1/2,2]} (1+sqrt(lambda))/omega(lambda).

This is finite: omega is continuous and strictly positive away from1, and omega(lambda)/sqrt(lambda)->24/125 at infinity. Therefore

 k+tr(Q sqrt B)<=c_omega Omega(B).                         (1)

## Trace of the actual bad Jacobian block

Since 0<q'<1, q(t)<=q(0)+|t| for every real t. Functional calculus gives K<=q(0)I+|L|. Operator concavity of square root and E L²=B give

 E|L|=E sqrt(L²)<=sqrt B.

Thus E tr(QK)<=q(0)k+tr(Qsqrt B). The Frobenius Cauchy-Schwarz bound and Gaussian Cauchy-Schwarz give

 |E tr(Q(J-K))|<=sqrt(k) epsilon.

Consequently

 E tr(QJ)
 <=q(0)k+tr(Qsqrt B)+sqrt(k)epsilon
 <=(q(0)+3/2)c_omega Omega(B)+epsilon²/2.                 (2)

The final coefficient is deliberately loose: use sqrt(k)epsilon<=(k+epsilon²)/2, and bound both k and tr(Qsqrt B) by their sum in(1). At source coefficients Omega<=2000delta and epsilon²<=1000delta, so(2) is at most C delta with an absolute finite C. There is no Bop or dimension dependence.

Square-root concavity is a standard matrix fact, but it can be checked here directly without an external theorem assumption: for Z>0,

 sqrt Z=(1/pi) integral_0^infinity t^(-1/2) Z(tI+Z)^(-1) dt.

The map Z -> (tI+Z)^(-1) is operator convex, hence Z(tI+Z)^(-1)=I-t(tI+Z)^(-1) is concave. Inverse convexity follows from the Schur-complement characterization of the positive block matrix [[H,I],[I,H^{-1}]] and taking convex combinations. Integrating yields concavity; regularize Z by eta I, apply Jensen to finite/simple approximations, and pass to the limit. The required moments exist since E||L||F²=tr B<infinity.

## The exact Schur orientation that is controlled

In the P,Q decomposition, positive definiteness of J implies

 J_QP (J_PP)^(-1) J_PQ <= J_QQ.

Taking trace and expectation and applying(2) yields

 E|| (J_PP)^(-1/2) J_PQ ||F² <= C delta.                (3)

This is an actual mixed-block energy bound at every deficit, using the inverse GOOD block. If P=0, the mixed term is zero; if Q=0, the claim is vacuous. For nontrivial P, J_PP is positive definite pointwise. Integrability of the mixed quadratic form follows from the Schur domination, so no uniform inverse bound is assumed.

It is NOT the differently oriented statement

 E tr[J_PQ (J_QQ)^(-1) J_QP]<=Cdelta.

That other expression is bounded pointwise by J_PP, whose trace can be order m. It cannot be substituted into(3) merely by cyclicity: the inverse is different. Accordingly, eliminating bad variables by a partial Legendre transform produces a good-space correction that this argument has not bounded. Eliminating good variables gives the paid orientation but does not by itself extract the desired many good exponential factors.

## Remaining transport obligation

No bound on E||J_PQ||F² follows from(3) without upper control of J_PP. Such control is not supplied by PBP<=2P: applying q to a compressed pencil is not justified, and mixed spectral effects remain. The intended next interface is a convex/conditional or transport argument converting(3), the retained covariance gap, and Jacobian compatibility into partial-factor error. No such interface is proved here. This note does not replace the frozen all-deficit target by a weighted derivative statement.
