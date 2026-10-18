# r54: cut, negative-type, and all-metric tree selection

Pre-freeze author research. No nominee. Source174 is developed history, not
an untouched family. A possible sharper all-metric routing construction is
being tested; no completed construction or frozen theorem is claimed.

## Operative source and paid templates

Both source174 companions were retrieved against the complete pinned tree.
The existence paper introduction/sparsification were read fully. The
algorithmic introduction, main-theorem, fractional_rounding and iteration were read fully;
tree_geometry1-245 and extraction1-78 were read. Other downloaded sections
are not claimed read. The source's geometric cone N consists of centered
positive-semidefinite Z for which d_Z(u,v)=b_uv^T Z b_uv satisfies the triangle
inequality. It already contains every cut metric and all squared Euclidean
metrics that satisfy triangle inequalities. Doubled distance profiles supply
an arbitrary-metric auxiliary geometry, but the spectral inputs remain PSD.

The actual step gives, for the SAME selected edge subset A,
 L_A <= (1/2)L_H + epsilon X,
 sum_{e in A} z_e z_e^T >= (1/2-epsilon)I,
with X tested above by3L_H on N. The rank-preserving auxiliary frame certifies
a surviving tree packing. Thus for every Z in N the selected edge energy is
at most (1/2+3epsilon) times the old energy, and iteration gives a final tree
with O(1/k) energy domination on N. This is an immediate strengthening already
contained in the source proof operations, not a new substantial theorem.
The source explicitly gives simultaneous one-cost/cut rounding, and arithmetic
r4 already identified ordinary disjoint thin-tree packing as routine.

Arbitrary spectral tests are not a legitimate upgrade: Anari--Oveis Gharan
1411.4613v4, Figure3 and surrounding text, give k-edge-connected planar
multigraphs for which every spanning tree contains an edge of resistance
near1. Their Theorem1.5 requires uniformly small effective resistances.
I05 already credits the expander/Ramanujan application as paid.

## All-metric energy and routing

For connected finite G with unit edge capacities and A subset of its edges,
let rho_G(A) be the least maximum edge load of fractional simultaneous flows
routing one unit between the endpoints of every edge of A. Undirected loads
count absolute traversal of each edge for each commodity. Cycles may be
removed, so distributions on simple paths suffice. The finite multicommodity
LP dual gives exactly

 rho_G(A)=sup_d [sum_{uv in A} d(u,v)]/[sum_{uv in E(G)} d(u,v)],

where d ranges over nonnegative pseudometrics with positive denominator.
One can use metrics and take limits. For one direction, every path has
length at least its endpoint distance, giving demand energy <= congestion
 times capacity energy. Conversely the path-flow LP dual assigns nonnegative
lengths to graph edges; shortest-path closure does not increase the total
capacity energy and preserves the dual demand distances. This is the
classical all-demand flow/metric duality, not a new result.

Linial--London--Rabinovich, The geometry of graphs and some of its algorithmic
applications, Section4 Theorem4.1 (statement and complete proof read), gives
an O(log(number of commodities)) flow-cut gap for arbitrary nonnegative
demands in undirected networks. Apply it to the n-1 tree-edge demands of a
source C/k-cut-thin tree. This gives rho_G(T)<=O(log n/k), and direct routing
gives rho_G(T)<=1. This is a routine paid transfer. It is not a nomination.

## Exact girth barrier and an explicit dual metric

Let G be finite connected SIMPLE, with n vertices, m edges, and girth at least
g>=3. Let A subset E have s>0 edges. Assign length g-1 to edges in A and1 to
all other edges, and let d be the resulting shortest-path metric. Then

 d(u,v)=g-1 for uv in A, and d(u,v)=1 for uv in E minus A.

Indeed a simple alternative path avoiding an edge in A has at least g-1
edges, all of length>=1; the direct edge itself has length g-1. Every edge
outside A has direct length1 and no nontrivial path can have length<1.
Consequently

 rho_G(A) >= s(g-1)/(m+s(g-2)).                         (1)

An independent primal proof: in any routing of congestion a, a given demand
edge carries at most a of its own demand directly. Its other paths have
length>=g-1. If a<=1, summing path lengths gives total load >=
s[g-1-a(g-2)], while capacities give total load<=am. Rearrangement gives
(1). If a>1, (1) is automatic since s<=m and its RHS<=1.

For a tree s=n-1. For a k-regular graph, m=kn/2, so the lower bound has scale
min(1,g/k). This is a conditional formula for every such graph; no new
construction of regular high-girth connected graphs is claimed here.

For a putative half-step s=m/2, (1) is (g-1)/g. Hence no all-metric
half-sparsification theorem with contraction1/2+o(1) can hold at large girth.
This is stronger than saying that the source proof does not yet handle an
extra cone: the corresponding near-half all-metric statement is false.
For approximate half size s/m->1/2 the same conclusion tends to1 as g grows.
No source cut/PSD assertion is contradicted.

## Why the PSD inference fails

A general metric need not be squared Euclidean. The five-point shortest-path
metric of K_{2,3} has cross-part distances1 and within-part distances2. For
x=(3,3,-2,-2,-2), sum x_i=0 and x^T D x=12>0. Its centered distance Gram
matrix Z=-JDJ/2 therefore has x^T Z x=-6<0. Thus Z is not PSD.
Taking P=xx^T gives P>=0 but trace(PZ)<0. Therefore testing a PSD order
inequality against the centered matrix of an arbitrary metric is invalid.
An isometric distance-profile realization in l_infinity, even one with exact
radial identities as in the source, does not change that matrix-order fact.

## Construction attempts and exact remaining obligation

A possible genuinely stronger scale for simple k-edge-connected graphs is
min(1, log n/[k log(k+1)]), motivated by the girth scale log n/log k.
This is a PROVISIONAL question, not a frozen scope, proved bound, optimality
claim, or absence-of-prior-art assertion. For multigraphs with enormous
parallel multiplicities that expression would need a different convention;
no such convention is silently imposed. No target is weakened from an earlier
freeze: none has occurred here.

The natural attempt was to retain the source packing frame and supplement
each halving by routes of the selected edge demands through the discarded
edges. Inequality(1) rules out the required near-half congestion even if the
selected subset is chosen optimally. Composing those routings cannot be
justified by the source's bounded product of near-half losses. A successful
construction would need to choose the final sparse tree and its routes in
one coupled argument, paying a cycle-length factor only once. Merely finding
short cycles is not enough: simultaneous uses compete for the same edges,
and their load must be bounded without destroying a surviving spanning tree.
No such coupled selection/routing estimate has been proved.

The cost-and-cut source corollary supplies a tree for each single cost
functional. Minimax can convert this to a distribution with appropriate
average edge use, but that does not select one tree satisfying every metric
cost bound. Interchanging the single-tree minimum with the metric supremum
would be an additional, unproved operation. Packing trees already supplies
small average direct demand; this does not settle the individual-tree routing.

At present there is no credible complete constructive theorem or nomination.
These exact route obstructions are technical support, not campaign credit.
