# Frozen author statement: quantitative selection into a metric shell

This scope was fixed after the prefreeze calculations and operative source/selected-primary/project-original reading, and before extended author proof. Authorized Codex / GPT-6 Astra / high / default service tier. SOURCE337 at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and its operative proofs are stipulated true. This is a nominee for independent review; no correctness, contribution, acceptance or count is assigned.

For each integer n>=3 let omega_j be the volume of the Euclidean unit j-ball and define

    s=(n+1)omega_(n+1),       c=1/((n+1)s^(1/n)),       q=(n+1)/n,
    lambda_n=min{1/4, (2^q-2)/2},
    mbar=s(1+lambda_n)^n,
    a0=s(n+1)^n/(4 n^n 3^(n+1)),
    b=omega_n/2^(n-1),       r0=(a0/b)^(1/n),
    D=3 r0(mbar/a0+1),       gamma=n(n+1)/(n+2).

For 0<=lambda<=lambda_n put

    H=1+lambda,
    C=H^(2n/(n-2)),
    epsilon_n(lambda)=C-1+(D^2/2)sqrt(gamma(C-1)),
    Psi_n(lambda)=2 max{(mbar epsilon_n(lambda)/b)^(1/(n+2)),
                       (mbar epsilon_n(lambda)/(b r0^n))^(1/2)}.

All these constants are dimension-only; Psi_n(0)=0 and Psi_n(lambda)->0 as lambda->0.

Let X be any proper CAT(0) space, with no bound on its ambient dimension. Integral currents and their mass are in the metric-current convention of the pinned CAT(0) source. Let T be any nonzero compactly supported integral n-current in X with boundary zero; arbitrary integer multiplicities are allowed. Write V_X(S) for the infimum of masses of compactly supported integral (n+1)-currents with boundary S. Set

    R_T=(M(T)/s)^(1/n),
    L_T=c M(T)^q=omega_(n+1) R_T^(n+1),
    delta=1-V_X(T)/L_T.

Assume 0<=delta<=lambda_n^2 and put lambda=sqrt(delta), H=1+lambda. There exist a nonzero compactly supported integral n-cycle A and a compactly supported integral (n+1)-current Q in X, with

    boundary Q=A-T,             M(Q)<=lambda L_T,
    1-lambda-lambda^2 <= (M(A)/M(T))^q <= 1+lambda.

Let nu=||A||/M(A), let o be the unique CAT(0) barycenter of nu in X, and set

    rho=(M(A)/s)^(1/n)/H.

Then support A is connected, diam(support A)<=D rho, and

    integral_X (d(o,x)/rho-1)^2 dnu(x) <= epsilon_n(lambda),
    |d(o,x)/rho-1| <= Psi_n(lambda)       for every x in support A.

In particular the radius satisfies

    R_T (1-lambda-lambda^2)^(1/(n+1))/H
       <= rho <= R_T (1+lambda)^(1/(n+1))/H.

The statement includes delta=0, where A may be chosen equal to T and Q=0. It asserts neither flatness of the metric sphere nor proximity to a Euclidean ball current, nor control of the support of T. It gives no claim for n=1 or n=2, unbounded-support currents, nonproper spaces, or a quantitative version of the frozen full Q286 question. All old full scopes and dispositions remain unchanged.
