# Attempts at the unchanged all-vertex target

T188U remains unresolved. None of the following conditional interfaces is a substitute theorem.

## 1. The sixth-moment interface

Fix a good prefix and vertex v. Put d=deg_G(v), W=Z_v/d, mu=E[W|G], q=(1+2D)^(-1/2). The paid r29 one-root calculation gives mu=(1+o(1))q uniformly in G,v. It also gives d q/sqrt(n)->1/sqrt(2) uniformly. Hence it would suffice to prove, uniformly over good G and v,

    E[(W-mu)^6|G] = o(q^6/n).                                (1)

Markov and the union bound then prove the all-vertex conclusion conditionally, and the source's superpolynomially small bad-prefix event removes conditioning. This reduction preserves every integer n and every vertex.

For example, the following stronger estimates would suffice, but ARE NOT PROVED here. For 2<=j<=6 suppose the conditional cumulants obey

    |kappa_j(W)| <= C_j D^(30(j-1)) d^(1-j).                  (2)

The standard centered sixth-moment identity is

    E(W-mu)^6 = kappa_6 +15 kappa_4 kappa_2
                 +10 kappa_3^2 +15 kappa_2^3.

Under (2) its absolute value is at most a constant times

    D^150 d^-5 + D^120 d^-4 + D^90 d^-3.

Multiplying by n q^-6=O(n D^3), with d~n^(1001/2000) and D~n^(1/1000), gives exponents respectively

    -2699/2000, -1758/2000, -817/2000,

all negative. This proves the implication (2)->(1), not (2). The integer30 merely exhibits a comfortable polynomial budget; it has no proven status as a collision exponent.

## 2. Exact connected-transcript identity

There is a precise algebraic cancellation mechanism which avoids charging every collision to the sixth moment. It is the classical moment-cumulant connectedness principle, applied to full decision transcripts.

For deterministic roots in a finite priority system, a completed query has finitely many possible comparison transcripts tau. A transcript records every exposed coordinate, its relative order wherever compared, the calls actually visited and the Boolean returns. Its event E_tau is a cylinder event in the deterministic finite coordinate set S_tau, and the successful transcript events partition {X=1}. Thus

    X_i = sum_{tau successful for root i} 1_{E_tau}.

Multilinearity gives an exact expansion of each joint cumulant as a finite sum of cumulants of cylinder indicators. For a fixed transcript tuple make a graph on the roots by joining i,j when S_tau_i intersects S_tau_j. If this graph is disconnected, the groups of cylinder indicators in its different components depend on disjoint sets of independent priorities. Their joint cumulant is zero.

For completeness, this last fact follows from the coefficient definition: the formal power series log E exp(sum_i t_i Y_i) is the sum of the logarithms for independent groups. Its coefficient of t_1...t_j vanishes if this monomial uses variables in more than one group. Expanding the logarithm also gives the explicit finite identity

    kappa(Y_1,...,Y_j)=sum_{partitions pi}
       (-1)^(|pi|-1)(|pi|-1)! product_{B in pi} E product_{i in B}Y_i.

Consequently only connected coordinate-overlap transcript tuples contribute to a cumulant. Centered moments are sums over partitions with no singleton blocks. Averaging the independent uniform star roots can be performed after these finite expansions; equivalently include their labels as independent private coordinates. This is a rigorous identity, not a probabilistic estimate of the surviving terms.

The missing estimate is substantial: an absolute bound for the connected transcript sums in the ACTUAL finite priority process, strong enough for (1) or (2). Each term of the partition formula involves one shared priority field inside each block and independent fields between blocks. It is therefore not automatically bounded by the source's independent-occurrence visitation law. A query may revisit a triangle within one root before meeting another root. After that self-collision its execution is not the independent unfolding. Charging all such histories to a single error reintroduces the floor in collision-floor.md. The source's first-collision lemma does not authorize continuing the same product estimate after a collision.

Even conditioning on a realized coordinate-overlap graph is not a valid shortcut: the condition that one transcript avoids another depends on its revealed priority values. Disjoint realized coordinate sets alone do not make the outputs conditionally independent. The cumulant expansion avoids that false assertion, but does not supply the required multi-collision count. No unexplained multiplication of first-collision probabilities is used here.

## 3. A different route: actual greedy-MIS concentration

The triangle continuation is a greedy matching on the 3-uniform triangle hypergraph, or a greedy MIS on its conflict graph J. Here vertices of J are triangles of G and adjacency means sharing a graph edge. On a good prefix,

    N=|V(J)|=(1+o(1))mD/3,
    maximum degree Delta <=3 max_e(d_e-1)<=6D.

For a fixed v give a triangle weight2 if it contains v and0 otherwise. The accepted weight is d-Z_v. Thus a concentration theorem for a locally supported weighted greedy MIS could prove the full target if its variance proxy were polynomial in D times the support size, rather than polynomial in D times N. This route uses the actual process and would bypass the independent-occurrence collision issue.

Here is what the inspected DMM theorem pays, and what it does not. In any fixed finite graph H, deleting a vertex a while retaining the same random ordering changes a root's original greedy answer only if its original recursive query visits a. Indeed, if it never visits a, all priority comparisons and recursive answers along the original trace are unchanged by deleting a; induction along that finite trace proves this claim. The number of affected roots is therefore at most one plus the total number of query paths beginning at a. DMM Theorem1.1 bounds the expectation of those paths by deg(a)/2. For any fixed weights in [0,1], writing F(H) for the expected accepted weight, we obtain

    |F(H)-F(H-a)| <=1+deg_H(a)/2.                            (3)

This is a coupling argument for the expectation, not a deterministic sensitivity bound on individual runs.

A first greedy pivot x is uniform among remaining vertices and leaves the induced graph H-N_H[x]. Applying (3) one vertex at a time gives

    |a_x+F(H-N_H[x])-F(H)|
       <= B_Delta :=1+(Delta+1)(1+Delta/2).                  (4)

The remaining random order is uniform, so the accepted weight so far plus F of the remaining induced graph is a martingale. It has at most N nonzero increments, each bounded by B_Delta. The ordinary bounded-increment martingale inequality therefore provides the global tail

    P(|accepted weight - F(J)|>=t)
       <=2 exp[-t^2/(2N B_Delta^2)].                        (5)

For weights in [0,2] rescale by2, changing only the constant. All implications (3)-(5) are valid for arbitrary finite graphs, conditional on the independently read DMM theorem; the concentration inequality is classical.

But (5) is too weak here: t of order sqrt(n) gives exponent only of order

    n/(mD *D^4) ~ n^(-1/2-11epsilon),

which tends to zero. The local weight support has size (1+o(1))dD/2, but it cannot replace N by declaration. DMM controls total incoming query paths for a fixed directed edge, summed over all roots. A weighted sum over a chosen set of ROOTS is a different index orientation. The proof's potential follows the first edge of a path; appending a child preserves that weight. Weighting its last/root vertex changes under extension and does not retain the same supermartingale calculation. No weighted local concentration bound is imported from that theorem.

The actual missing alternatives are now explicit: a finite-process connected-transcript estimate, or a local weighted concentration estimate with appropriate uniformity. Neither is proved or refuted by this packet. The solvable shared-triangle model is a diagnostic for the first alternative and is not a finite-process independence premise.
