# T373E135 exact scope

This is an author research scope, frozen before extended proof drafting. No correctness, contribution, acceptance or count is assigned.

Fix ANY integer d>=2 and real alpha>0. Use any fixed collection of the five neighborhoods, common central ball B, supporting potential u, and smooth diffeomorphisms Y_k,W_k (k=1,2) provided by Source373's Riesz construction at openai/math commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Its operative proof operations are stipulated true. Choose ANY a>0 such that Qbar=[-a,a]^d is contained in B and the maps extend as diffeomorphisms near Qbar. Set

 f(t)=Z^{-1} product_{j=1}^d exp(-2/(a^2-t_j^2)) for t in Q=(-a,a)^d,

and f=0 elsewhere, where Z normalizes the integral to one. Write nu=f dt and

 mu=nu/3+(Y_1#nu+W_1#nu+Y_2#nu+W_2#nu)/6.

Let c_alpha(x0,x1,x2)=sum_{i<j}|xi-xj|^{-alpha}, with value infinity at collisions, and E=min_{pi in Pi(mu,mu,mu)} integral c_alpha dpi. For epsilon>0 define

 E_epsilon=min_{pi in Pi(mu,mu,mu)} [integral c_alpha dpi + epsilon KL(pi|mu tensor mu tensor mu)],

using KL(P|Q)=integral log(dP/dQ)dP, infinity if P is not absolutely continuous with respect to Q. Let pi_epsilon denote its minimizer.

Put R=c_alpha-u(x0)-u(x1)-u(x2), and for k=1,2 define

 r_k(t0,t1,t2)=R(t0,Y_k(t1),W_k(t2)),
 K_k(t)=D^2_(t1,t2) r_k(t,t,t),
 H(f)=integral_Q f log f,
 C_* = log9-d log(2pi)-2H(f)+(1/4)sum_{k=1}^2 integral_Q f(t) log det K_k(t) dt.

All integrals and logarithms in C_* are finite, and each K_k is positive definite on Qbar. The result claims that E_epsilon is finite and has a unique minimizer for every epsilon>0, and as epsilon decreases to zero,

 E_epsilon=E+d epsilon log(1/epsilon)+C_* epsilon+o(epsilon),
 integral c_alpha dpi_epsilon=E+d epsilon+o(epsilon),
 KL(pi_epsilon|mu^3)=d log(1/epsilon)+C_*-d+o(1).

Moreover pi_epsilon converges weakly to the coupling pi_0 obtained by sampling t with law nu, choosing k uniformly from {1,2}, and uniformly permuting (t,Y_k(t),W_k(t)). This is the unique permutation-invariant unregularized optimizer. Other unregularized optimizers are not asserted unique.

No uniformity of remainders in d, alpha, a or the source geometry is claimed. No general all-density theorem, positive-everywhere marginal, arbitrary particle number, deterministic-regularity law, Gaussian fluctuation theorem for the actual entropic optimizer, higher-order expansion, optimal numerical constant, or literature-priority statement is included. Source nonattainment, the leading logarithmic order and weak selection alone are not proposed as independent findings. All old frozen scopes remain unchanged.
