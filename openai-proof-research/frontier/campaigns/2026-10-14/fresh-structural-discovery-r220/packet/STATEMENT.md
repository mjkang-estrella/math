# Frozen statement: quantitative rigidity of Lagrangian charts with Blaschke cut pairs

Author-proof research scope r220. This statement is an abstract matrix-chart consequence of Source344, not a near-Blaschke metric theorem. No correctness/contribution/acceptance grade or count is assigned.

Fix integers m,k>=1, d=m+k, q>=2, a real K>=1, D=pi/2, T=pi, r0=pi/64, and a real a with 0<a<D/2. The norm of a matrix is its Frobenius norm; inequalities between symmetric matrices are quadratic-form inequalities. For a matrix function on a closed interval, its C^q norm is the maximum over 0<=j<=q of the supremum of the Frobenius norm of its jth derivative.

Let A:I -> Sym_d(R), I=(0,D) union (D,T), be C^q, with blocks

A = [[V,C],[C^T,H]],  V of size k, H of size m.

Assume all of the following.

1. A'(t)>0 on I. H and C extend as C^q functions through D, with H'(D)>0. Set S=V'-C'(H')^(-1)(C')^T on I.
2. For all t in I, and by continuity at D for the first inequality,

   K^(-1) I_m <= sin²(t) H'(t) <= K I_m,
   K^(-1) I_k <= (sin²(2t)/4) S(t) <= K I_k.

3. There is a positive definite B in Sym_k(R), with K^(-1)I_k<=B<=K I_k, and symmetric C^q remainders R_0, R_D, R_T, such that

   A(t)=-I_d/t+R_0(t) for 0<t<=4r0;
   A(t)=-diag(B,0_m)/(t-D)+R_D(t) for 0<|t-D|<=4r0;
   A(t)=-I_d/(t-T)+R_T(t) for T-4r0<=t<T.

   The remainders extend to [0,4r0], [D-4r0,D+4r0], and [T-4r0,T], respectively, and each has C^q norm at most K. The C^q norms of A on [r0,D-r0] and [D+r0,T-r0] are also at most K.
4. For distinct x,y in I define

   Q(x,y)=V(y)-V(x)-(C(y)-C(x))(H(y)-H(x))^(-1)(C(y)-C(x))^T.

   Assume Q(u,u+D)=0 for every 0<u<D. The inverse exists because H'>0 on (0,T).
5. The nonnegative function

   f(x,y)=|det(A(y)-A(x))| / sqrt(det A'(x) det A'(y))

   on I times I, with its zero diagonal values, has a continuous extension to [0,T]^2.

Set

w(z)=sin^m(z) |sin(2z)/2|^k  (0<=z<=T),
Delta=integral_[0,T]^2 [f(x,y)-w(|y-x|)] dx dy,
A_mod(t)=diag(-2cot(2t) I_k,-cot(t) I_m),
C_* = R_D(D),
J_a=[a,D-a] union [D+a,T-a],
gamma=3/(4(d+9)),
delta_*=(min{r0,a/4})^(4(d+9)/3).

Then Delta>=0. There exists a finite constant C=C(m,k,q,K,a)>=1, independent of A and B, such that whenever 0<=Delta<=delta_*, simultaneously for every integer j with 0<=j<=q-1,

max_(t in J_a) || (d/dt)^j [A(t)-A_mod(t)-C_*] ||_F
    <= C Delta^(gamma(1-j/q)).

For j>=1 the derivative of C_* is zero. At Delta=0 the right side is zero. Thus the same one constant symmetric shear, explicitly C_*=R_D(D), works on both half-periods. No separate branch gauges, variable change of time, unspecified symplectic coordinate changes, or additional changes to the frozen hypotheses or conclusion are allowed.

The constant is quantified only as a finite uniform function of the displayed parameters; the asserted rate is the explicit displayed power. No optimality is claimed. The fixed compact set J_a excludes the poles; the residue B is free in the hypotheses, not fixed equal to I. No estimate at a pole, curvature estimate, metric norm, geometric realization, manifold classification beyond the paid source theorem, or assertion under a small global injectivity-radius/diameter ratio is included.
