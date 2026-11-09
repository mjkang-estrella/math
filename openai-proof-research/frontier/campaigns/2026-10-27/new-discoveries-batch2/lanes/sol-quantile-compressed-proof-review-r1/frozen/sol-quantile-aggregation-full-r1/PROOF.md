# A continuous counterexample to Conjecture 1

Provisional mathematical result for root adjudication; no acceptance, credit, formalization or priority claim.

## Literal source and scope

Chen–Liu–Liu–Wang, *Ordering and Inequalities for Mixtures on Risk Aggregation*, arXiv:2007.12338v2, Conjecture 1, printed p25, asserts for every n, every doubly stochastic matrix Lambda, and every tuple F in (M_D)^n that D_n(F) is contained in D_n(Lambda tensor F). Section 3, printed p7, defines (Lambda tensor F)^(-1)=Lambda F^(-1). Section 4.3, printed p11, defines M_D using decreasing densities on their support. D_n is the set of distributions of sums over arbitrary couplings, not just extremal quantiles. The symbol for inclusion is non-strict in this source.

The counterexample below has n=2 and Lambda with all four entries 1/2. Thus no assertion about products of T-transforms or factorization of general doubly stochastic matrices is needed.

## Exact continuous marginals

For k=1,2 define q_k(0)=0. On successive intervals [j/5,(j+1)/5], j=0,...,4, give q_k the respective slopes

    q_1: 1, 13/10, 22/10, 28/10, 29/10;
    q_2: 5/10, 9/10, 9/10, 16/10, 18/10.

Let F_k be the law of q_k(U), U uniform on [0,1]. These are continuous, atomless distributions. Their densities, on successive support intervals, are reciprocals of the displayed slopes. Each interval has mass 1/5. All slopes are positive and nondecreasing, so both densities are positive and nonincreasing on their full interval supports. The support endpoints are respectively

    F_1: 0, 1/5, 23/50, 9/10, 73/50, 51/25;
    F_2: 0, 1/10, 7/25, 23/50, 39/50, 57/50.

Thus F_1,F_2 belong to the literal required density class, not an atomic approximation to it. Both supports are compact; all integrability and tail issues are absent. Write r=(q_1+q_2)/2 and let G be the law of r(U). Then Lambda tensor (F_1,F_2)=(G,G), with r a strictly increasing quantile and Lipschitz constant 47/20.

## Test payoff and finite rational data

Let x_j=159j/1000 for j=0,...,20. Set h(0)=0 and define h to have slopes, on successive intervals [x_j,x_(j+1)],

    -1,-1,+1,+1,+1,-1,-1,-1,-1,-1,+1,+1,-1,-1,-1,-1,-1,-1,-1,+1.

Extend it constantly outside [0,159/50]. It is a bounded continuous 1-Lipschitz function. All possible sums considered here lie within this interval.

The explicit finite rational certificate is `certificate.json`. Its arrays `old_permutation` and `dual` are part of this proof, not instructions to trust a solver. Let N=200, u_i=(2i+1)/(2N), a_i=q_1(u_i), b_i=q_2(u_i), and z_i=r(u_i), for 0<=i<N. The certificate gives a permutation p of {0,...,199} and rational numbers d_0,...,d_199 with

    h(z_i+z_j) <= d_i+d_j                         (every 0<=i,j<200),
    A := (1/N) sum_i h(a_i+b_(p_i)) = -37597/400000,
    B := (2/N) sum_i d_i            = -519287/4000000.

All 40,000 inequalities and the two equalities are verified by `verify_math.py` using Python Fraction arithmetic only. The verifier independently reconstructs q_1,q_2,r,h, checks the permutation, density slopes, every rational inequality and every displayed rational total. It imports neither numpy nor scipy, calls no optimizer, and has no numerical tolerance. In particular no assertion of optimality of the discrete LP is required: any feasible d and any permutation giving these strict bounds suffice.

## A source coupling with a separating expectation

For U uniform on [0,1), on the interval [i/N,(i+1)/N) put

    V=U+(p_i-i)/N,   X=q_1(U),   Y=q_2(V).

The interval permutation preserves Lebesgue measure, so X~F_1 and Y~F_2. Denote the law of X+Y by H. Then H belongs to D_2(F_1,F_2). For every such U,

    |X-a_i| <= (29/10)/(2N),
    |Y-b_(p_i)| <= (18/10)/(2N).

The Lipschitz property gives the exact lower bound

    E h(X+Y) >= A - 47/4000.

## Upper bound valid for every continuous target coupling

Take any Z,W with both marginals G, with arbitrary dependence. Since r is continuous and strictly increasing, write Z=r(U'), W=r(V'), where U',V' each have the uniform distribution. Set I=floor(N U'), J=floor(N V'); endpoint null sets do not matter. Both I and J are uniform on {0,...,N-1}; their joint law is unrestricted. The rational certificate implies

    E h(z_I+z_J) <= E(d_I+d_J) = B.

Moreover |Z-z_I|+|W-z_J| <= 2(47/20)/(2N)=47/4000 almost surely. Hence, for EVERY coupling of G,G,

    E h(Z+W) <= B + 47/4000.

Finally

    A - B - 47/2000 = 49317/4000000 > 0.

Thus E_H h exceeds the expectation under every law in D_2(G,G). It follows H does not belong to D_2(G,G). This disproves the literal universal Conjecture 1. The certificate's strict gap survives both continuous error allowances; this is an exact continuous transport separation, not proof by a bounded grid experiment.

## Strongest classical-subsumption objection

The mechanism is ordinary Kantorovich weak duality plus a Lipschitz rounding estimate. Those are classical, and the finite certificate is a computed witness rather than a new transport theorem. The only proposed outcome is the refutation of this exact published conjecture with these actual continuous decreasing-density marginals. A prior counterexample to this same inclusion would subsume it completely; bounded searches do not establish worldwide novelty.

Source Theorem 1 (printed pp4–5) uses random permutations to obtain DISTRIBUTION mixtures. Its resulting marginals are mixtures of cdfs, rather than r(U). Source Theorem 3 (pp11–13), and Blanchet–Lam–Liu–Wang Theorem 1, optimize VaR/RVaR, not every bounded nonmonotone payoff h; they do not imply or preclude this separation. Source Proposition 1 compares convex-order hulls, which cannot detect this nonconvex h. Source Example 2 (p8) gives a known atomic counterexample, but those atoms are outside M_D. Our marginals have strictly positive densities on interval supports, so this is not that example renamed. Source Proposition 2 is for uniform marginals, n>=3 and complete averaging. Neither source marginal here is uniform. Source Example 3 (pp25–26) preserves existence of a constant sum under its mean-length hypotheses; it does not preserve the nonconstant law H.

The later joint-mixability paper 2204.11438v4, Theorem 1 and Theorem 3/Proposition 4, concerns conditional criteria for negative association and decompositions of constant-sum vectors. It supplies no all-sum-law inclusion. No use of its statements is necessary for the counterexample. No adaptation of a public complete resolution was found in the bounded inspected bodies; access and search limitations are in provenance.md and FAILURES.md.
