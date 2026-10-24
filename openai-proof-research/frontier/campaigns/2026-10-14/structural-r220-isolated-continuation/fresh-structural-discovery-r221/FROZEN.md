# Frozen candidate r221: parameter oscillation bound for loop-homology transients

This is an author candidate, conditional only on the stipulated truth of Source345 and its operative upstream inputs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. No correctness, contribution, acceptance or count is assigned here. This discovery statement is not a closed-geodesic counting assertion.

Let n>=3, let P be a nonempty finite simplicial polyhedron of dimension p>=0, and let t |-> g_t be a continuous map from P into the smooth Riemannian metrics on the standard sphere S^n, where continuity means the C^0 topology on metric tensors. Each metric is smooth in the sphere variable; no derivative in t is assumed. All homology has coefficients F_2. Put Lambda=H^1(R/Z,S^n) with its strong topology and let M be its constant loops. Set

    F_t(gamma) = (integral_0^1 |gamma'(s)|_(g_t)^2 ds)^(1/2),
    Y_a = {(t,gamma) in P x Lambda : F_t(gamma)<a},  a>0.

Let lambda(t)>0 be the reciprocal of the global mean frequency of (S^n,g_t;F_2): equivalently lambda(t)=lim_(m->infinity) cr_(g_t)(Theta^m)/(2m(n-1)), with Theta the sphere product class of degree 3n-2 and cr the homological critical level in the F_t filtration. Write lambda_- = min_P lambda(t), lambda_+ = max_P lambda(t), and omega=lambda_+-lambda_-.

For k>=0 let beta_k be the infimum of all D>=0 such that, for every a>0,

    ker[H_k(Y_a)->H_k(P x Lambda)]
      is contained in ker[H_k(Y_a)->H_k(Y_(a+D))].

Define beta_k^rel by replacing these groups with H_k(Y_a,P x M), H_k(P x Lambda,P x M), and H_k(Y_(a+D),P x M). The infimum is +infinity if there is no such D.

THEOREM.
(1) There exist D_0>0 and R>=0, depending on the family but independent of t, a and homological degree, such that every fiber's global-null homology class dies after the F_t increment D_0 (absolutely and relative to M), and every nonzero homogeneous z in H_q(Lambda) has

    |cr_(g_t)(z)-q*lambda(t)| <= R.

The function lambda is continuous; in particular 0<lambda_-<=lambda_+<infinity.

(2) For any D_0,R as in (1), simultaneously for all k>=0,

    beta_k <= k*omega + C,
    beta_k^rel <= k*omega + C,
    C = (2p+3)*D_0 + lambda_+ + p*lambda_- + 2R.

In particular a family with constant global mean frequency has a single additive death bound in all homological degrees for the total parameter space, including relative to P x M. All conclusions use open sublevels and allow arbitrary degeneracies in the individual metrics.

(3) The coefficient of k*omega cannot be decreased uniformly over these families. For every n>=3 and b>1, let h be the unit round metric (sectional curvature 1), let P=[-1,1], and set

    g_t = (b-(b-1)*t^2)^2 h.

Then omega=(b-1)*pi/(n-1). For every integer m>=1, with k_m=n+2m(n-1),

    beta_(k_m) >= 2*pi*m*(b-1),
    beta_(k_m)^rel >= 2*pi*m*(b-1).

Consequently limsup_(k->infinity) beta_k/k = omega and limsup_(k->infinity) beta_k^rel/k = omega for this family.

The quantities beta count neither parametrized loops, critical circle orbits, prime geodesics, geometric images nor distinct lengths. They measure death of globally null homology in an explicitly defined total-space filtration. Constants are existential and family dependent, not an algorithmic estimate from finite metric data. No normalization by volume, diameter or curvature is imposed on the general family. The unit round normalization is used only in (3).
