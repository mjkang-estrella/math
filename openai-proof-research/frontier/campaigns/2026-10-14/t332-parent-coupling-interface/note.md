# A simultaneous-coupling interface for the unchanged T332 problem

Author-side exploratory work by Myeongjin Kang, no affiliation; original prose CC BY 4.0. This is a conditional finite interface, not a nominated result or a solution of T332. No acceptance credit or novelty claim is made. The full unrestricted real-tree target in analytic-r39 remains unchanged.

## Conditional finite lemma

Let T be a finite combinatorial tree with positive edge lengths and all its branching vertices included. Let mu_1,...,mu_n be probability measures on its vertices. Suppose a joint coupling (X_1,...,X_n) with these marginals satisfies, for every i,j,

    E d_T(X_i,X_j) <= r W1(mu_i,mu_j).

Then for every reversible stochastic A with stationary probability pi and every integer t>=1, there are vertex-supported probabilities nu_i such that

    sum_i pi_i W1(mu_i,nu_i)^2
      + t sum_ij pi_i A_ij W1(nu_i,nu_j)^2
    <= 3024 r^2 sum_ij pi_i (t^(-1) sum_(s=1)^t A^s)_ij W1(mu_i,mu_j)^2.

The constant3024 and the smoothing operation are paid by pinned source332. The coupling hypothesis is additional; it has NOT been established uniformly for arbitrary finite metric trees.

Proof. The joint coupling is a probability on the finite set Omega=V(T)^n. Omit its zero-weight atoms and write lambda_omega for its atom weights. Root T, and let T_e be the component beyond edge e, whose length is w_e. Encode the ith coordinate of the coupling by the real ell-one vector

    v_i(omega,e)=lambda_omega w_e 1_{X_i(omega) in T_e}.

The tree cut formula gives

    ||v_i−v_j||_1 = E d_T(X_i,X_j) <= r W1(mu_i,mu_j).

Apply the source's ACTUAL expected-coordinatewise-median construction, not merely its existential cotype conclusion, to v_1,...,v_n. For p=1/(t+1), q=t/(t+1), let G=p sum_(s>=0) q^s A^s. For each i, let J_1,J_2,J_3 be independent with law G_i, independent of omega. The source's output is

    u_i=E_J med(v_(J_1),v_(J_2),v_(J_3)).

For fixed omega and J, the coordinatewise majority of the rooted edge-cut indicators is precisely the cut vector of the tree median m(X_(J_1)(omega),X_(J_2)(omega),X_(J_3)(omega)). The median belongs to V(T), since all branching vertices are included. This follows cut by cut: removing e splits the tree into two convex components, and its median lies in the component containing at least two of the three points.

Let nu_i be the law of this tree median when omega has weights lambda and J has the indicated law. Summing u_i(omega,e)/w_e over omega gives exactly nu_i(T_e). Similarly summing v_i(omega,e)/w_e gives mu_i(T_e). Hence, by the triangle inequality separately on every edge,

    W1(mu_i,nu_i) <= ||v_i−u_i||_1,
    W1(nu_i,nu_j) <= ||u_i−u_j||_1.

Insert these inequalities and the input-distance bound into the source cotype estimate for its specified u_i. This proves the displayed inequality.

The crucial order is to apply the source estimate in the enlarged ell-one space indexed by (omega,e), then average back. It retains the square of the first moment, (E d_T(X_i,X_j))^2. Applying a point-valued estimate separately for each omega and averaging would instead introduce E d_T(X_i,X_j)^2, the uncontrolled quantity identified in analytic-r39. This conditional interface avoids that particular Jensen loss, provided the simultaneous first-cost coupling can be supplied.

## What the checked primary comparison does and does not supply

Li–Anantharam, arXiv1908.01388v2, defines the pairwise coupling ratio for exactly this first-cost objective. Theorem17 bounds it by7.56 for complete separable ULTRAMETRIC spaces. Proposition18 gives a bound23.1 log n for a finite collection of n measures on a complete separable metric space. Proposition5 records optimal quantile coupling on the real line. These statements do not give a uniform bound for arbitrary tree metrics: a path already need not be ultrametric, and n is unrestricted here. The primary statements were read; their complete proofs were not read in this pass. URL: https://arxiv.org/html/1908.01388v2

Searches also located metric-labeling results for hierarchically separated trees and a different result for tree-shaped QUERY graphs. Neither distinction may be erased: a tree of labels is not a tree of query indices, and a general tree need not have geometrically separated edge lengths. Those search leads have not been adopted as new dependencies.

## Outstanding work

A universal simultaneous-coupling construction for arbitrary weighted trees would establish the above cotype conclusion uniformly for finite vertex-supported measures. It is an unproved sufficient route, not asserted necessary. General complete nonproper trees, arbitrary Radon probability measures, and the final all-Hilbert-domain extension step still need their full scope justified even if the finite coupling is achieved. No restriction to paths, ultrametrics, bounded depth, finite targets or an n-dependent constant will replace T332.
