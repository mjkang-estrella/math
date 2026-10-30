# Target and status

Status: NO NOMINATED DISCOVERY; credit 0. This document contains failed-route analysis and a conditional reduction, not a solution.

Gladkov, [arXiv:2408.08457v2](https://arxiv.org/html/2408.08457v2), Definitions §2 and Conjecture 10.2, printed p19: G is a locally finite connected simple graph, with independent edge states of arbitrary probabilities p_e in [0,1], and distinct fixed terminals a,b. Let X be the maximum number of edge-disjoint open a–b paths. With

    Phi_k(z) = 1 - exp(-z) sum_{j=0}^{k-1} z^j/j!,

let lambda_k satisfy Phi_k(lambda_k)=P(X>=k). The target is lambda_{k+1}<=lambda_k for all positive integers k. All nondegenerate parameters are finite and unique since Phi'_k(z)=exp(-z)z^(k-1)/(k-1)!>0 for z>0. Endpoint conventions do not supply a counterexample. The author's currently retrieved DecisionTrees.pdf also retains the conjecture.

For locally finite graphs, X is bounded by the deterministic degree of a. Each event X>=k is the increasing union of its finite-subgraph versions, because finitely many witnessing paths have finite union. Consequently a universal finite-graph proof would extend by continuity of Phi_k and its inverse, including extended endpoint limits. No finite-graph proof was obtained.

# Conditional Poisson-to-simple-graph reduction

Let H be any finite undirected base graph with independent capacities C_e~Poisson(r_e), r_e>=0 finite. For fixed k, replacing every C_e by min(C_e,k) preserves {maxflow>=j} for every j<=k: any cut below j has all its summands below j, while clipping any summand at k cannot reduce a cut previously at least j below j. Integer maxflow/mincut applies.

For N>=max r_e, replace each base edge uv by N private length-two paths u-w_{e,i}-v, with independent first edge probability r_e/N and second edge probability 1. This is a finite simple graph, even when H has parallel edge labels, since all intermediate vertices are distinct. The effective capacity of that bundle is Bin(N,r_e/N). Suppressing the private degree-two vertices preserves terminal flow: an effective unit uses one open two-edge branch, and any collection of terminal paths projects to capacity-respecting walks, whose cycles may be erased.

Independent binomial capacities converge in joint total variation to the Poisson vector. One may use the safe elementary bound 2 sum_e r_e^2/N, obtainable by coupling each Bernoulli(r_e/N) with a Poisson(r_e/N) and taking a union bound. Deterministic integer capacities can likewise be represented by that many always-open private paths.

Suppose a STRICT witness lambda_k<lambda_{k+1} were found for the Poisson model. Choose c strictly between these parameters. Then

    P(X>=k) < Phi_k(c),    P(X>=k+1) > Phi_{k+1}(c).

For sufficiently large N the same strict inequalities hold in the finite simple replacement, by the total variation bound. The two positive margins specify how large N must be. Rational approximation of r_e and c preserves strict margins, and finite binomial probabilities are rational; exponential comparisons could then be rigorously certified. This is a conditional transfer, not a witness: neither numerical model produced its required strict inequality. No particular finite N or graph refuting Conjecture 10.2 is asserted.

# Exact obstruction to universal ultra-log-concavity

Consider s,h,t, private vertices u_i,v_i (1<=i<=1000), and only these edges:

* s-u_i open with probability 12/5000; u_i-h always open;
* h-v_i open with probability 41/5000; v_i-t always open.

The graph is connected and simple. Its flow is min(A,B), with independent A~Bin(1000,12/5000), B~Bin(1000,41/5000). Let N=1000,D=5000, and define integer tail numerators

    T_a(0)=D^N,
    T_a(j)=D^N-sum_{i=0}^{j-1} binom(N,i) a^i(D-a)^(N-i), 1<=j<=3.
    Q_j=T_12(j)T_41(j)-T_12(j+1)T_41(j+1), 0<=j<=2.

Then q_j=P(X=j)=Q_j/D^(2N). The exact integer certificate proves

    -1/10000 < q_1^2 - 2 q_0 q_2 < -1/100000.

ULC of a probability mass sequence requires j q_j^2 >= (j+1)q_{j-1}q_{j+1}, so this graph violates ULC already at j=1. Reproduce with `python exact_obstructions.py`; no transcendental evaluation or numerical sign decision is used in these assertions. Decimal q-values in its JSON are explanatory only. This result is a proof-route obstruction with no novelty claim, no discovery credit, and no assertion that this graph violates implied-parameter monotonicity.

# Why the weaker generic facts do not finish the proof

A geometric variable Y with P(Y>=k)=2^-k has multiplicative, hence log-concave, tails. Nevertheless lambda_1=log(2), and

    Phi_2(log2)=(1-log2)/2 < 1/4=P(Y>=2),

because log2=integral_1^2 dx/x>1/2. Hence lambda_2>lambda_1. This is a distributional obstruction only: Y is NOT asserted to be an edge-disjoint-path flow. It rules out an argument based solely on these generic tail properties.

Van den Berg's [1996 marked-Poisson paper](https://ir.cwi.nl/pub/2208/2208D.pdf), theorem p422 and proof pp423–425, gives a two-event disjoint-occurrence product bound. The proof partitions space and removes splitting errors; it does not establish the adjacent inverse-tail comparison needed here.

Huh's [2015 paper](https://web.math.princeton.edu/~huh/hVectorMatroids.pdf), Theorem 3 and Corollary 4, concerns log-concavity of matroid h- and f-vectors under a characteristic-zero representability hypothesis. No identification of those coefficients with the distribution indexed by FLOW VALUE k was obtained. Reliability coefficients indexed by number of retained edges are different objects. Treating them as the required flow law would leave an unproved bridge.

The accepted OpenAI proposition `cmp:joint` at pinned commit 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a applies to finite independent labelled hyperedges with arbitrary probabilities and node sets A,T, A nonempty:

    P(o<->A and o<->T) >= P(o<->A) min_{a in A} P(a<->T).

It is accepted as true here. It controls connectivity events, and no deduction to the distribution of maximum edge-disjoint multiplicity was established. Its cone lemma and exploration setup were inspected rather than relying only on the catalogue. No upstream theorem is challenged.

# Numerical limits

For the Wheatstone edges s-u=A,s-v=B,u-t=C,v-t=D,u-v=E, exact integer capacities give

    X=min(A+B,C+D,A+D+E,B+C+E).

For the triangle model, the three relays have all source and sink attachments and all three pairwise relay edges; its eight source–sink cuts are enumerated. The source files specify every rate vector, deterministic seed, probability filter and clipping threshold. Independent residual-flow checks agree with cut enumeration in 600 integer configurations and preserve thresholds in 3000 clipping checks. These checks validate implementations but are not universal proofs.

No numerically negative implied gap passed the trigger filter. Most importantly, tiny positive gaps near a Poisson limiting cut do not certify any inequality. There is no validated route from these diagnostics to the universal conjecture. No formalization was started.
