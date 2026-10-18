# Interior atoms do not improve the finite-vertex cotype optimization

Author-side support for unchanged T332. Myeongjin Kang, no affiliation; original prose CC BY 4.0. This is a technical reduction, not a separate nominee, independent review, or priority claim.

Let K be the geometric realization of a finite tree with positive edge lengths and vertex set V containing all branching points. There is a 1-Lipschitz map

    R : (P1(K), W1) -> (P(V), W1)

that fixes every probability supported on V. Consequently, for any finite tuple of vertex-supported input laws, allowing cotype witnesses at arbitrary interior points of K does not improve the optimal cotype objective. The same holds for witnesses in a larger complete real tree containing K as a convex subtree: gate to K first.

## Construction and proof

For a vertex v put r(v)=delta_v. If x lies on an edge [u,v] of length l, at distance s from u, put

    r(x)=(1-s/l)delta_u+(s/l)delta_v.

The definitions agree at endpoints. On a single edge, coupling the common endpoint mass and transporting the remaining mass along that edge proves

    W1(r(x),r(y)) <= d(x,y).

For arbitrary x,y, subdivide their unique tree path at the intervening vertices. Apply the preceding inequality on each segment and the triangle inequality. The segment lengths add to d(x,y), so r is 1-Lipschitz on all of K. Only this upper bound is needed.

Define R(mu) by averaging r(x) against mu. This is an ordinary finite-dimensional integral: each of its finitely many vertex coefficients is a continuous piecewise-affine function on K. Thus R(mu) is a probability on V and R fixes P(V).

For completeness, contraction can be proved without choosing transport plans measurably over x,y. Let f:V->R be 1-Lipschitz for the tree distance and let E f(x)=sum_v r(x)(v)f(v). On every edge this interpolant is affine with slope of absolute value at most1; summing along tree paths proves E f is 1-Lipschitz on K. For any coupling gamma of mu and nu,

    |sum_v f(v)[R(mu)(v)-R(nu)(v)]|
      = |integral [E f(x)-E f(y)] dgamma(x,y)|
      <= integral d(x,y) dgamma(x,y).

Infimizing over gamma and using finite Kantorovich duality on V proves W1(R(mu),R(nu))<=W1(mu,nu). The finite duality is the ordinary finite transportation linear-program dual; it entails no nonseparable or measurable-selection assumption here.

Now fix vertex-supported inputs mu_i and nonnegative weights pi_i and b_ij. Consider the objective

    J(nu)=sum_i pi_i W1(mu_i,nu_i)^2
           + sum_ij b_ij W1(nu_i,nu_j)^2.

R fixes each mu_i and contracts both kinds of distance, hence J(R nu)<=J(nu). The infimum over vertex-supported witnesses therefore is at most the infimum over arbitrary K-supported witnesses. The reverse inequality follows from inclusion. Both infima are equal. For the cotype objective take b_ij=t*pi_i*a_ij. This argument uses only nonnegativity of the coefficients; reversibility is unnecessary for the reduction.

If K is a finite convex subtree of a larger complete real tree T, its nearest-point gate pi_K is 1-Lipschitz and fixes the input supports. The map R composed with gate pushforward has the same properties. Thus permitting witnesses elsewhere in T likewise cannot lower this fixed-input objective.

This is not a claim that P(V) and P1(K) have the same cotype constant for a fixed unsubdivided V: general input laws in P1(K) need not be supported on V. It says that finite-vertex inputs can always be given finite-vertex witnesses without losing any estimate. Uniform estimates over all finite subdivisions still must be proved. In particular, the unresolved constrained probability-flow problem is not made artificially harder by restricting its witnesses to the chosen finite vertex set.
