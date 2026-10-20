# Frozen scope K369R134 — signed radial reciprocal boundary kernels

Freeze status: author-proof candidate only; no correctness, contribution, acceptance, count, formalization, manuscript or release verdict.

Let D={z in C: |z|<1}. All circle integrals use ordinary arclength dtheta, of total mass 2pi. Let G be the Dirichlet Green kernel of -Delta on D and P_s(z)=(1-|z|^2)/(2pi|z-s|^2). For a real measurable radial potential q(z)=v(|z|) with 0<Q=||v||_L-infinity(0,1)<infinity and e>=0 small, set T_e f(z)=e integral_D G(z,x)q(x)f(x)dx. Define the Poisson kernel K_e and off-diagonal boundary interaction kernel N_e by the absolutely dominated Green-resolvent series

 K_e(p,s)=P_s(p)+sum_{j>=1}(T_e^j P_s)(p),
 N_e(s,t)=1/(pi|s-t|^2)+e sum_{j>=0} integral_D P_s(x)q(x)(T_e^j P_t)(x)dx,  s!=t.

These are the kernels of -Delta-eq with Dirichlet boundary condition. Define
 D_e(s,t)=K_e(0,s)K_e(0,t)/N_e(s,t) for s!=t, and D_e(s,s)=0.

There is an absolute constant c>0 with the following property. For every Q>0, every 0<delta<=Q, and every such v with ||v||infinity=Q satisfying, for every integer k>=0,

 integral_0^1 v(r)(1-r^2)^4 r^(2k+1)dr
 >= delta integral_0^1 (1-r^2)^4 r^(2k+1)dr,                         (M)

all 0<e<=c delta/Q^2 have these conclusions:

(a) The stated kernels are well-defined at the stated arguments, K_e(0,s)>0, N_e(s,t)>0, and D_e is a continuous conditionally negative semidefinite kernel on S^1. It is strictly conditionally negative definite on every finite set of distinct circle points: for every m>=2, distinct s_1,...,s_m and real a_1,...,a_m not all zero with sum_i a_i=0, sum_ij a_i a_j D_e(s_i,s_j)<0.

(b) Put f_e(theta)=1/N_e(1,exp(i theta)) for theta not in 2pi Z and f_e(0)=0. With Fourier convention fhat_e(n)=(2pi)^-1 integral_0^(2pi) f_e(theta) exp(-in theta)dtheta,

 fhat_e(1)<=-pi/2,
 fhat_e(n)<=-(pi/4)e delta *12/[(n-1)n(n+1)(n+2)(n+3)] for every integer n>=2.

At e=0, D_0(s,t)=|s-t|^2/(4pi), which is conditionally negative semidefinite; finite-set strictness at e=0 is not claimed.

(c) Conversely, for any real bounded radial v, if D_e is conditionally negative semidefinite for a sequence of positive e tending to zero, then integral_0^1 v(r)(1-r^2)^4 r^(2k+1)dr>=0 for every integer k>=0. This necessity does not assert sufficiency when some moments vanish or when their normalized infimum is zero.

In particular (a)–(b) apply to v(r)=r^2-b for every 0<b<1/6, with delta=1/6-b and Q=1-b. These potentials change sign on D. If b>1/6, then D_e for that v fails conditional negative semidefiniteness for all sufficiently small positive e. No assertion at b=1/6 is included.

Scope is the center-normalized boundary kernel for bounded radial potentials and small coupling. No claim is made for off-center normalization of signed potentials, nonradial signed potentials, arbitrary coupling, full reciprocal inertia of interior Green matrices, Neumann eigenfunctions, or a complete Pick RKHS with an infinite diagonal kernel. The existence quantifier for the universal constant c is the exact constant claim; no numerical value or optimality is claimed.
