# Frozen active target SOUP: SK Ornstein–Uhlenbeck free-energy path

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Source family217 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. This is the sole eligible active target. The earlier family262 scope is retained without modification in screened-out-p3r/original-scope.md and is ineligible, not a substitute result.

For every fixed real beta>1 and every n>=2, let g_ij(t), 1<=i<j<=n, t in R, be independent two-sided stationary standard real Ornstein–Uhlenbeck processes with covariance

    E[g_ij(s)g_ij(t)] = exp(-|t-s|).

Define the zero-field Gaussian Ising SK log partition function using the counting spin prior,

    F_(n,beta)(g) = log sum_(sigma in {-1,1}^n)
                       exp[(beta/sqrt(n)) sum_(i<j) g_ij sigma_i sigma_j],
    Z_(n,beta)(t) = n^(-1/6) [ F_(n,beta)(g(t n^(-2/3))) - E F_(n,beta)(g(0)) ].

Full target: for every beta>1 there exists a Borel probability law P_beta on C(R;R), with the topology of uniform convergence on compact intervals, such that the laws of Z_(n,beta) converge to P_beta as n tends through **all integers**. The law is stationary and reversible, has mean-zero one-point marginal sqrt(a2(beta))*nu_beta (the stipulated family217 constants/law), and is temporally nonconstant in the precise sense

    there exists t_beta>0 with E_(P_beta)[(Z(t_beta)-Z(0))^2]>0.

No Gaussianity, Markov property, explicit covariance formula, independent increments, universality in non-Gaussian couplings, temperature uniformity, heat-bath dynamics, high-temperature or critical-beta limit is asserted. The full-sequence law and temporal nonconstancy are both required. A subsequential limit, tightness, a covariance representation or a conditional mixed-moment criterion does not satisfy this target. No numerical evidence or source theorem is stipulated to prove a new clause.

counted=false. Any mathematical or contribution gate is independent and still outstanding. If unresolved, the entire scope above remains unpaid; it is not narrowed to tightness or a frozen process.
