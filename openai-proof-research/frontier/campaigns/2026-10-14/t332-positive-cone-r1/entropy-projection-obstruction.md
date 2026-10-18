# Weighted relative-entropy projection also fails uniformly

Myeongjin Kang, no affiliation. Original prose CC BY4.0. This excludes one explicit alternative positivity operation, not all retractions or the unchanged T332 theorem. No new-to-literature or acceptance claim.

The parent has excluded ordinary fixed-p nearest projection. A different candidate is the information projection of a strictly positive edge vector x onto the cone K, minimizing

    D(q|x)=sum_e w_e [q_e log(q_e/x_e)-q_e+x_e],

with the continuous value at q_e=0. This is a strictly convex coercive objective; it has a unique minimizer on the closed convex cone, and fixes every feasible strictly positive x. Its derivative uses adaptive curvature w_e/q_e. The following three-edge example gives an unbounded Lipschitz ratio in the required weighted edge ell1 metric.

## Exact cone and optimizer

Take a unit stem, one unit child edge, and a second child edge of length epsilon>0. Thus

    K={(r,z,s): z,s>=0, r>=z+s},
    N(r,z,s)=|r|+|z|+epsilon |s|.

Fix a>0 and set q0=(1+a,1,a), a feasible strictly positive point. For delta>0 set x(delta)=(1+a,1,a+delta), so N(x(delta)-q0)=epsilon delta. There is a unique lambda(delta)>0 solving

    (1+a)exp(lambda)=exp(-lambda)+(a+delta)exp(-lambda/epsilon).     (1)

The difference of left and right sides is strictly increasing in lambda; it is negative at0 and positive for sufficiently large lambda. Define

    r=(1+a)exp(lambda), z=exp(-lambda),
    s=(a+delta)exp(-lambda/epsilon).                              (2)

Then r=z+s and all coordinates are positive. The gradient of D at q=(r,z,s) is

    (log(r/(1+a)), log z, epsilon log(s/(a+delta)))
       =lambda(1,-1,-1).

Its pairing with every feasible y is nonnegative, and its pairing with q is zero. Hence the convex first-order inequality proves that q is the global minimizer on K. Strict convexity proves uniqueness. No assumption that the optimum occurs in a prescribed symmetric family is used.

## Unbounded local sensitivity

At delta=0 the solution is lambda=0 and q=q0. The implicit function theorem applies because the lambda derivative of (1) is positive. Differentiating gives

    lambda'(0)=1/(2+a+a/epsilon).

At0 the derivatives of (r,z,s) are

    ((1+a)lambda', -lambda', 1-a lambda'/epsilon).

The third derivative is positive. Therefore the right derivative at0 of N(q(delta)-q0) is

    (1+a)lambda'+lambda'+epsilon(1-a lambda'/epsilon)
       =epsilon+2lambda'.

The local Lipschitz ratio of this projection at q0 is consequently at least

    1+2/[epsilon(2+a+a/epsilon)].                               (3)

Take a=epsilon^2 and let epsilon tend to0. The expression diverges. Thus weighted relative-entropy projection is not a universal Lipschitz retraction for arbitrary positive edge lengths, even with only three edges. The whole calculation takes place at strictly positive coordinates and uses arbitrarily small positive delta, so no choice of boundary extension can repair the failure.

## What this leaves open

A successful positivity map need not minimize any divergence. A different tree-dependent optimization rule is not excluded by this example. In particular, neither this note nor the l1 projection obstruction establishes an unbounded lower bound for all retractions. The known path rearrangement deliberately moves non-nearest flows and remains valid. The task still requires either a genuinely different globally stable construction or a multi-point obstruction applying to every retraction.
