# A general obstruction to the augmented-frame repair

Author research support only. This is NOT the frozen T174D theorem, a counterexample to T174D, an independent review, or a nomination. All source statements remain stipulated. The construction below refutes the attempted implication that adding a head-incidence frame to the source's cut/rank frames makes its matrix halving certify directed reachability. Classical positive-weight whitening, contraction limits and matrix concentration are credited operations.

## Statement

For every odd integer m>=3 let r=2m and n=2m+1. There is a loopless directed multigraph B on n vertices, with a root o, which is the labelled union of r arc-disjoint spanning out-arborescences rooted at o. There is an Eulerian r-arc-connected directed multigraph D containing B. For every rho in (0,1] there are:

* source-form rank-preserving vectors z_e=s_e M b_e on R^(n-1), s_e>0 and M invertible, satisfying sum z_e z_e^t=I and ||z_e||^2<=(1+rho)/r;
* head vectors h_e=e_head(e)/sqrt(r) on the n-1 nonroot vertices, satisfying sum h_e h_e^t=I;
* cut vectors a_e=X^(-1/2)b_e on R^n, where X=L_B+I/n, so X>=L_B, cut indicators have X-energy at most twice their B-cut size, and sum a_e a_e^t<=I;
* a subset A of the actual labelled arcs of B with no incoming arc to a nonempty subset S not containing o,

such that, for w_e=(a_e,z_e,h_e), Sigma=sum w_e w_e^t, and d=3r+1,

 0<=Sigma<=3I,  ||w_e||^2<=5/r,
 || sum_(e in A) w_e w_e^t - Sigma/2 ||
 <= sqrt(30 log(4d)/r)+9/r.                                      (1)

Thus the error is o(r^(-1/4)), even for the FULL stacked matrix including its cross blocks. Scaling w by sqrt(2/3) gives the source normalization Sigma<=2I. There is no arborescence rooted at o contained in A. The statement is universal in odd m, though its asymptotic relevance is at large m. No numeric sample establishes it.

## 1. Graphs and explicit directed packing

Vertices are o, s_1,...,s_m and t_1,...,t_m. Put S={s_i}. B has:

1. two copies of each arc s_i -> s_j, i!=j;
2. m parallel arcs o -> t_i for each i;
3. m parallel arcs s_i -> t_i for each i;
4. two parallel arcs t_i -> s_i for each i.

Every nonroot vertex has indegree r=2m; the root has indegree zero. The arc count is 4m^2=r(n-1).

Index r trees by (j,b), j in {1,...,m}, b in {0,1}. Tree (j,b) uses the b-th copy of t_j->s_j and all b-th copies of s_j->s_l for l!=j. For each i, choose a set Q_i of exactly m of the 2m tree indices containing (i,0),(i,1); this is possible for m>=3. In those trees attach t_i using a distinct o->t_i arc; in the remaining m trees attach it using a distinct s_i->t_i arc. These assignments use all labelled arcs exactly once. The selected entrance t_j always has its o->t_j arc. Hence every s_l is reached through o,t_j,s_j, and every remaining t_i is attached to either o or a reached s_i. Each tree has one incoming arc per nonroot vertex and no directed cycle, hence is an out-arborescence. This proves the packing without using a packing theorem.

Obtain D by adding m copies t_i->o and m-2 copies t_i->s_i for each i. It is the symmetric digraph with two arcs in each direction on every S-clique pair, and m arcs in each direction on every link o--t_i and s_i--t_i. It is Eulerian.

To check r-arc-connectivity, take a nontrivial cut and complement it if necessary so o is outside. Let a=|U intersect S|. If 1<=a<=m-1, the S-clique contributes 2a(m-a) outgoing arcs. Each s_i inside forces at least m more outgoing arcs across its two-link path s_i--t_i--o, regardless of which side t_i occupies. Thus the outgoing cut is at least 2a(m-a)+ma. This concave quadratic has minimum at an endpoint a=1 or m-1; those values are 3m-2 and (m-1)(m+2), both >=2m for m>=3. If a=m, the paths alone contribute m^2>=2m. If a=0, nontriviality forces at least one t_i inside, whose two links contribute 2m. Thus every outgoing cut has at least r arcs. This D is a valid host in the frozen target, but because it is symmetric T174D for this D is already a routine source consequence. It is not a counterexample to the target.

## 2. A legitimate source rank frame

Give every internal S arc weight M0>0. Give every o->t_i arc weight (m-2)/m and every arc between s_i,t_i weight m/(m+2), independent of its direction. Write L(M0) for the weighted undirected Laplacian and work on 1-perp. Set

 z_e=sqrt(weight_e) L(M0)^(-1/2) b_e.

All weights are positive and the graph is connected. Therefore the z frame is exactly isotropic and preserves the rank of every edge subset. Choose b_e with its actual direction; signs do not change subset rank or the diagonal covariance.

We justify the uniform limiting squared norm 1/r as M0 tends to infinity. Decompose 1-perp into the (m-1)-dimensional zero-sum subspace supported on S and its orthogonal complement. In this decomposition L(M0) has upper-left block 4m M0 I+O(1), fixed off-diagonal blocks, and a positive-definite complementary block. Block inversion shows that the upper-left inverse block is (4m M0)^(-1)I+O(M0^(-2)) and the off-diagonal inverse block is O(M0^(-1)). Hence an internal arc has weighted resistance tending to 2/(4m)=1/(2m).

For a fixed outside arc, the inverse quadratic form converges to its resistance after contracting S. This also follows by minimizing the resistor energy over potentials: the 4m M0 term forces equal S potentials, and block inversion gives the same limit. The contracted network is K_(2,m), with terminals o,s and intermediate vertices t_i; each o--t_i link has total conductance a=m-2 and each s--t_i link has conductance b=m.

For completeness, the effective resistance of o--t_i in that network is

 R_ot=(a+b/m)/(a(a+b)),

because the direct conductance a is parallel to the series path consisting of conductance b from t_i to s and aggregate conductance (m-1)ab/(a+b) from s to o. Multiplying by a gives a R_ot=(a+b/m)/(a+b)=1/2. Interchanging a,b gives b R_st=(b+a/m)/(a+b)=1/2+1/m. There are m original root arcs and m+2 original s--t arcs per link. Each individual original arc therefore has limiting weighted resistance 1/(2m)=1/r.

There are finitely many arcs. Choose one finite M0 so all their squared z norms are at most (1+rho)/r. The M0 may depend on m,rho; no effective rate is claimed or needed. This supplies genuine positive finite weights, not an invalid singular-limit frame.

## 3. Cut and head frames

The cut matrix X=L_B+I/n is positive definite and dominates L_B. For a nontrivial cut U,

 1_U^t X 1_U=|delta_B(U)|+|U|/n <=2|delta_B(U)|,

because B is connected. On 1-perp, inverse order bounds the a norms by ordinary B effective resistance. For an outer arc there are at least m parallel undirected copies, so its resistance is <=1/m=2/r. On S, the unweighted graph has four parallel edges per clique pair; its resistance is 1/(2m)=1/r, and adding the other edges only decreases it. Thus ||a_e||^2<=2/r and sum a_e a_e^t<=I.

Every nonroot indegree in B equals r, so the displayed head frame is isotropic and each ||h_e||^2=1/r. Stacking three covariance-bounded frames gives Sigma<=3I by (x+y+z)^2<=3(x^2+y^2+z^2). Together with rho<=1, each ||w_e||^2<=5/r.

## 4. Selection, including all cross blocks

For each unordered S pair independently choose a fair sign: retain both copies of one directed orientation, and discard both copies of the reverse orientation. Retain (m-1)/2 of the o->t_i copies and (m+1)/2 of the s_i->t_i copies. Retain NO t_i->s_i copy. Every choice leaves delta_A^-(S) empty.

For an internal pair, put P=w_(i->j)w_(i->j)^t and Q=w_(j->i)w_(j->i)^t; the two copies in a direction have identical w. The pair's full covariance is 2P+2Q, the selected covariance is either 2P or 2Q, and the centered contribution is a Rademacher sign times E=P-Q.

Since P^2=||w_(i->j)||^2 P and likewise for Q,

 E^2 <=2(P^2+Q^2)<=(10/r)(P+Q).

The first inequality follows from (P+Q)^2>=0, or by expanding 2(P^2+Q^2)-(P-Q)^2=(P+Q)^2. Summing internal pairs gives sum E^2 <=(10/r)(Sigma/2)<=15I/r. All E are fixed real symmetric d by d matrices; the pair signs are independent. Tropp, *User-friendly tail bounds for sums of random matrices*, arXiv:1004.4389v7, Theorem4.1 (Rademacher case, norm bound(4.4)), therefore gives

 P(||sum signs*E||>=t) <=2d exp(-r t^2/30).

At t=sqrt(30 log(4d)/r) the bound is 1/2. Hence a choice with the internal centered norm at most t exists. Tropp's theorem and its mgf proof are classical antecedents; this is a direct application with its variance hypotheses verified.

For the deterministic outer discrepancy write Sigma_R,Sigma_O,Sigma_I for root arcs, outgoing s_i->t_i arcs, and incoming t_i->s_i arcs, respectively. It is

 -Sigma_R/(2m)+Sigma_O/(2m)-Sigma_I/2.

The first two terms have norm at most 3/(2m), since Sigma_R+Sigma_O<=Sigma<=3I.

In the a principal block of Sigma_I, the incoming arcs comprise exactly 2/(m+2) of the full s_i--t_i covariance, so that block is <=2I/(m+2). The same is true in the z block, because the weights are equal within each parallel pair. In the h block it is (1/m) times the projection onto S. The block-stacking inequality consequently gives ||Sigma_I||<=6/m. Its half has norm at most 3/m. The total deterministic error is <=9/(2m)=9/r. This bound includes all off-diagonal blocks, by the stacking inequality; it is not a blockwise-only assertion.

Adding the internal and deterministic bounds proves (1). The subset has no entry to S and so cannot contain any rooted out-arborescence. This completes the supporting obstruction.

## Consequence and limits

For large r, (1) is smaller than any fixed positive multiple of r^(-1/4). Thus neither separate nearly-half graphic/head covariances nor their full stacked nearly-half inequality ensures even one root-reachable spanning subgraph. Our B also has the source's actual r-tree packing, finite positive rank frame, small-resistance cut frame, and a valid Eulerian supergraph D. This is a precise failure of the proposed extra-head-frame implication.

It does NOT show every good matrix outcome loses reachability, does not rule out choosing a different packing or conditioning selection on incoming cuts, and does not refute any stipulated source statement. It does not disprove T174D. The directed selection operation remains unpaid.
