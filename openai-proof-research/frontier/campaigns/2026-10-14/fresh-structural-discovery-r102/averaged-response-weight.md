# Constant response weight from retained separation

Active author deduction, collaborating with the parent. Parent supplied the separation-slack idea and the derivative approximation; averaging before comparing A with L is this lane's proposed way to avoid Bop. No independent review or full all-deficit claim.

Let ell(a)=log q(a), so ell'=d=q-a>0. Set

 L_log=sup_a |q''(a)|/d(a)<infinity,
 L_F=sup_a |q''(a)|<infinity.

Finiteness follows from smoothness and the tails: at positive infinity q''=O(a^-3), d~a^-1; at negative infinity q'' is polynomial times the Gaussian density and d~|a|. These scalar tail facts are the parent's derivative-support calculation; no additional numerical constant is required here.

Write Z_r=partial_r A=X_r+G_r, G_r=partial_r Y. In an eigenbasis of A, the Frechet derivative Dq(A)[Z_r] has coefficient q[a_i,a_j]. Since q' is L_log-Lipschitz in ell, averaging q' on[a_i,a_j] gives

 |q[a_i,a_j]-q'(a_i)|<=L_log |ell(a_i)-ell(a_j)|.

The retained weight r_ij>=1/16 therefore yields

 E sum_r ||partial_r J-q'(A) Z_r||F² <=16 L_log² C_sep.       (1)

Also |q'(a_i)-q'(a_j)|<=L_log|ell(a_i)-ell(a_j)| gives

 E sum_r ||[q'(A),Z_r]||F²<=16 L_log² C_sep.                 (2)

Because 0<q'<1, replacing Z_r by X_r in(1)-(2) incurs only the H1 norm of Y, without Bop. Define the CONSTANT symmetric matrix M=E q'(A), 0<M<I, and tensor H_rij=E partial_r J_ij. The actual transport is a gradient, so H is fully symmetric. Jensen and(1) show

 sum_r ||M X_r-H_r||F²
 <=32 L_log² C_sep+2||gradient Y||².                       (3)

Equation(2) similarly gives

 sum_r ||[M,X_r]||F²<=32 L_log² C_sep+8||gradient Y||².     (4)

All quantities are finite. The derivative tensor is L2 by(1), boundedness of q', and A in Gaussian H1, so its expectation is legitimate; its symmetry also holds distributionally. The source retained estimate makes the right sides O(delta).

## Only O(delta) directions can have small M

The scalar q' is increasing, q'(0)=2/pi, and q'>0. Thus q'(t)+q'(-t)>=2/pi. Applying functional calculus to L and using x->-x gives

 N:=E q'(L)>=1/pi I.

Frobenius functional-calculus Lipschitzness with constant L_F and Jensen yield

 ||M-N||F²<=L_F² E||A-L||F²=L_F²||Y||².                 (5)

Consequently the spectral projection R=1_{(0,1/(2pi))}(M) has

 rank R <=4pi² L_F²||Y||²=O(delta).                    (6)

Indeed every unit eigenvector of M in this subspace has quadratic form of N-M at least1/(2pi); summing and using the squared Frobenius norm proves the count. No multiplication of q'(A)-q'(L) by X_r occurs in(5).

## Exact triple-index symmetry identity

In an M eigenbasis with eigenvalues m_i, let T_rij=(X_r)_ij and W_rij=m_i T_rij. The tensor T is symmetric in its last two indices. The parent's algebraic identity is

 m_j(T_rij-T_irj)
 =(m_j-m_i)T_rij+(m_i T_rij-m_r T_irj)+(m_r-m_j)T_irj.  (7)

Each right-side term is an antisymmetry component of W, using the last-two symmetry of T for the first and last terms. Thus(3) bounds the squared sum of the left side by a universal multiple of delta. In particular, on any triple where the common third index has m_j>=c>0, the ordinary symmetry defect of T is controlled by C delta/c². Restricting all indices to the well-conditioned M subspace gives a full symmetrization estimate with an absolute constant.

A soft version is also exact: let f:[0,1]->[0,1] obey f(t)/t<=C_f, and let U=f(M)^tensor3 T. Multiplying(7) by f(m_r)f(m_i)f(m_j)/m_j gives the ordinary antisymmetry of U bounded in total squared norm by C C_f² delta. Averaging over the six index permutations therefore produces a fully symmetric cubic within O(delta) squared distance of U.

## Remaining restrictions

Neither(6) nor the soft tensor symmetrization proves that removing those input directions has O(delta) transport cost. The corresponding coefficient energy can involve large B, and M need not commute with B. No gap is assumed at an arbitrary M spectral cutoff. The soft-cutoff tensor has not been shown to approximate the original weighted primitive. Nor has the retained separation yet been converted into a dimension-uniform all-density associativity/rounding estimate. These are the current unresolved interfaces, not consequences hidden in the word removal.
