# T372L127 — frozen full target

Frozen after the preselection calculations recorded in prefreeze.md and before writing the attempted proof. This file is to remain byte-for-byte unchanged. It is a target, not a theorem certification.

Let Omega be any bounded connected open subset of R^3 with C-infinity boundary. Fix c>0 and M>0. For a scalar function on the closure, use the maximum of the suprema of the absolute values of all Cartesian derivatives of order at most 1000 as its C^1000 norm.

For j=1,2 let lambda_j,mu_j be arbitrary real C-infinity functions on the closure of Omega such that

    mu_j >= c,                 3 lambda_j + 2 mu_j >= c,
    ||lambda_j||C^1000 + ||mu_j||C^1000 <= M.

Let Lambda_j:H^(1/2)(boundary Omega;C^3)->H^(-1/2)(boundary Omega;C^3) be the full static physical displacement-to-traction operator for

    div[lambda_j (div u) I + mu_j (grad u + (grad u)^T)] = 0.

Fix the Sobolev norms once for Omega. Put delta=||Lambda_1-Lambda_2|| in that operator norm and define omega_alpha(0)=0 and

    omega_alpha(t) = [log(3+1/t)]^(-alpha),     t>0.

The target asserts: for EVERY such Omega,c,M there exist C<infinity and alpha>0, depending ONLY on Omega,c,M and the fixed Sobolev norms, such that EVERY pair above satisfies

    ||lambda_1-lambda_2||L-infinity(Omega)
      + ||mu_1-mu_2||L-infinity(Omega) <= C omega_alpha(delta).

There is no boundary agreement, prescribed collar, smallness, symmetry, analyticity, finite-dimensional parametrization, selected sequence, unknown gauge, or added measurement. The constants must be uniform over the entire displayed finite-regularity-bounded smooth class. They may not depend on higher derivatives, an individual pair, a pair-selected compact set, or delta. Both Lamé coefficients and the full physical operator are retained. No explicit numerical alpha is asserted.

This target is relative to the stipulated pinned source theorem statements and proof operations, with new quantitative deductions requiring proof. It does not assert arbitrary-patch recovery or stability for the different metric/connection target Q of I112.
