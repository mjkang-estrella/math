# Arbitrarily large graph-level counterexamples with explicit integer weights

Status: proved below from the exact Kron-scale pair criterion; symbolic and independent rational verification accompany this note. Historical novelty remains unverified.

## The theorem

For every integer k≥2, let G_k be the join K_k ∨ I_(k+1): k mutually adjacent hubs, k+1 pairwise nonadjacent outer vertices, and every possible hub–outer edge.

Assign conductance 1 to every hub–outer edge and conductance a to every hub–hub edge, where

0<a≤1/[k(k−1)].

Then:

1. The normalized resistance capacity is submodular.
2. Every one of the k hubs has strictly negative resistance curvature.
3. No strictly positive conductance assignment on this support can make all curvatures nonnegative.

Consequently Conjecture 7.7 has counterexamples of every odd order n=2k+1≥5, and the number of negative-curvature vertices is unbounded. This strengthens a single five-vertex counterexample to an explicit infinite family of non-RN supports admitting submodular capacity.

At the endpoint a=1/[k(k−1)], a common scaling gives particularly simple **integer conductances**:

hub–hub edges: 1;
hub–outer edges: k(k−1).

Their curvatures are

p_hub=−(k−1)/(2k³),
p_outer=(2k−1)/(2k²).

The count of zero elementary submodularity gaps is exactly C(k+1,2)·2^(k−1); every other elementary gap is strictly positive.

## Proof of the graph-level non-RN obstruction

Let H be the set of k hubs and O the set of k+1 outer vertices. A spanning tree has 2k edges, and every edge has at least one endpoint in H. Hence in every spanning tree T,

∑_(v∈H) deg_T(v)=2k+e_H(T),

where e_H(T) counts its hub–hub edges. Under arbitrary strictly positive conductances, every spanning tree has positive probability. Hub–hub edges exist and each belongs to some spanning tree, so E[e_H(T)]>0. The resistance-curvature identity yields

∑_(v∈H) p_v
=k−(1/2)E[∑_(v∈H)deg_T(v)]
=−(1/2)E[e_H(T)]<0.

Thus at least one hub is negatively curved for *every* positive weighting of this graph. This conclusion is independent of the symmetric weights used to establish the submodularity premise.

## Exact resistance and curvature formulas

Put m=k+1 and D=m+ak. Decomposing the Laplacian into hub differences, outer differences and the difference of the two group constants gives

R_hh'=2/D,
R_oo'=2/k,
R_ho=(D+k−1)/(kD).

The full curvatures are

p_hub=−a(k−1)/(2D)<0,
p_outer=(2+ak)/(2D)>0.

This also verifies the endpoint formulas after substituting a=1/[k(k−1)].

## Submodularity proof at every Kron scale

The exact pair criterion says that for any reduced vertex set T of at least three vertices and any pair i,j∈T, write

A=L^T_ii>0, B=L^T_jj>0, c=−L^T_ij≥0,
u=p^T_i, v=p^T_j.

The sign of the corresponding nonempty-base capacity gap is the sign of

c{2ABuv+c(Bu²+Av²)}.

Pairs of curvatures with the same sign automatically pass. Empty-base gaps are always nonnegative by resistance-radius monotonicity. It therefore suffices to handle opposite-sign pairs in every Kron reduction.

Retain h hubs and l outer vertices. Cases h=0 or l=0 are uniform complete graphs, so all their curvatures are positive. Suppose h,l≥1. Set

A₀=2/D,
B₀=2/k,
C=(D+k−1)/(kD),
U=A₀(h−1)/h,
V=B₀(l−1)/l,
Q=2C−U−V>0.

Solving the two symmetry-class equations R[T]p^T=r(T)1 and ∑p^T=1 gives

p^T_hub=(C−V)/(hQ),
p^T_outer=(C−U)/(lQ).

Here

C−U=(2+ah)/(Dh)>0,
C−V=[2D−l(2+ak)]/(kDl).

Equivalently, the retained curvatures have the more compact closed form

Z=h(D−l)+kl>0,
p^T_hub=[2D−l(2+ak)]/(2Z),
p^T_outer=k(2+ah)/(2Z).

These identities were independently confirmed by the structural-theory agent.

### Case 1: at least one outer vertex is eliminated, l≤k

Then

2D−l(2+ak)≥2D−k(2+ak)=2−ak(k−2)
≥2−(k−2)/(k−1)=k/(k−1)>0.

Thus *every* reduced curvature is positive. The pair criterion is automatically satisfied.

### Case 2: all m=k+1 outer vertices are retained

Let 1≤h≤k and E=m+ah. Eliminating the k−h omitted hubs gives exact reduced parameters

p^T_hub=−a(k−1)/(2E),
p^T_outer=(2+ah)/(2E),
c_ho=D/E≥1,
L^T_oo=k−(k−h)/E≤k.

Only hub–outer pairs have opposite curvature signs. For such a pair set u<0<v and B=L^T_oo. Since A>0,

2ABuv+c(Bu²+Av²)
≥A v(c v−2B|u|).

Furthermore

2E(c v−2B|u|)
=c(2+ah)−2Ba(k−1)
>2−2ka(k−1)
≥0.

The strict inequality follows from a>0, h≥1 and c≥1. Therefore every opposite-sign pair passes strictly. Same-sign pairs pass automatically. This proves submodularity at every Kron scale, hence on the full Boolean lattice.

## Equality count

All reduced curvatures above are strictly positive or strictly negative; none vanish for a>0 in the stated range. The pair numerator is positive for same-sign pairs whenever c>0, and it is strictly positive for every opposite-sign pair by the previous estimate. Thus a nonempty-base gap vanishes exactly when its reduced pair has c=0.

The only missing edges in a reduced graph are outer–outer edges when *all* hubs have been retained. Eliminating even one hub creates positive outer–outer conductances. Therefore a zero gap consists of two added outer vertices and a base containing every hub, together with an arbitrary subset of the other k−1 outer vertices. Its count is C(k+1,2)·2^(k−1).

Empty-base gaps are strictly positive because their two-vertex radius is strictly smaller than r(V): the full curvature vector has no zero coordinates, so deleting the other vertices has strictly positive quadratic deletion loss. Thus there are no additional equalities.

## Limits of the conclusion

The negative-curvature vertex count grows without bound, but the endpoint curvature magnitude decreases with k. This theorem does not establish arbitrarily large negative curvature or a uniform negative bound. It proves explicit arbitrarily large support-level counterexamples, with all nonlinear weight quantifiers in the non-RN conclusion removed by the spanning-tree identity.

## Corollary: full-dimensional robustness on each support

For every k≥2, the integer weighting above lies in an open neighborhood in the space of all strictly positive edge conductances on G_k such that every weighting in that neighborhood has submodular capacity. This is an open region of dimension

|E(G_k)|=k(k−1)/2+k(k+1)=(3k²+k)/2.

No symmetry, equality of spoke weights, or equality of hub-edge weights is required within this neighborhood. The graph-level non-RN conclusion holds throughout it, since it holds for every positive weighting on this support.

### Proof

The zero elementary gaps identified above are structural. Their two added vertices are outer vertices and every hub is retained. Under **any** positive weighting on this support, eliminating other outer vertices cannot create an outer–outer edge: every path between retained outer vertices passes through a retained hub. Thus the reduced pair conductance c remains zero, and the exact gap remains zero identically.

Every other elementary gap is strictly positive at the displayed symmetric weighting. There are finitely many such gaps, and each varies continuously with positive conductances. Therefore they remain strictly positive on a common open neighborhood. All structural zero gaps remain zero there. This proves submodularity throughout that neighborhood.

The result concerns openness relative to the fixed support's positive edge-weight space. Adding new outer–outer edges changes the support and is not covered by this corollary.
