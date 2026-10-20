# Exact marginals and cut-thin spanning trees: r136 prefreeze derivation

Myeongjin Kang; no affiliation. Original research notes, 2026-10-20.
Runner: Codex / GPT-6 Astra / high reasoning / default service tier.

**PREFREEZE; no nominee.** The universal question below was not proved or disproved, and no theorem scope was frozen. The elementary deductions and exact examples here record the work actually completed. They are not a substitute nomination, a contribution rating, a correctness gate, or an acceptance. Pinned source statements and their proof operations are stipulated true.

## 1. The direction and its precise scope

Let G be a finite connected loopless undirected multigraph, with labelled edge set E, at least two vertices, and spanning-tree polytope P(G), defined as the convex hull of its tree incidence vectors. For x in P(G), every nontrivial cut has x(delta(S)) >= 1. Put

    a_x(T) = max_{empty != S != V} |T intersect delta(S)| / x(delta(S)),
    H_A(x) = {1_T : T is a spanning tree and a_x(T) <= A}.

The exploratory question was whether there is an absolute A such that

    x belongs to conv H_A(x) for every G and every x in P(G).       (Q)

It asks for a distribution supported entirely on thin trees with E[1_T]=x, not merely a high probability event, a tree for each cost, or bounded marginal inflation. Arbitrary real x is meaningful in this existence question; there is no algorithmic claim. The rational and real cases are equivalent by approximating convex coefficients by dyadic coefficients and using compactness, as detailed below.

The archived r54 question is about simultaneous metric demand routing. T174D in r107 is a frozen rooted directed arborescence question. Neither is being resumed or weakened. The preliminary family-180 route was abandoned on actual Hamiltonian affine-span/counting history before developing a target there.

## 2. Strongest paid reduction: source plus primary operations

Use the two authenticated family-174 manuscripts at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The algorithmic companion's cor:ta-fractional-rounding gives, for rational x with all cut masses at least one and any nonnegative cost c, a positive-support tree with

    a_x(T) <= K,             c(T) <= K c.x,                K=24B,

where integer B >= max(1,C) is fixed from thm:tt-algorithm. This is already simultaneous cost-and-cut rounding. Its entire proof was read: pair aggregation, truncation at one, scaling by 2n^2, floors, repeated deletion under residual-connectivity control, least-cost selection, and lifting to a cheapest positive original edge. Oveis Gharan–Saberi arXiv:0909.2849v4 Proposition 5.1 already supplies the deletion-and-cheapest-selection operation. Its full proof was read directly. The initial read was v3 Proposition 5.4; the version check and v4 proof read occurred after the first derivation draft, before sealing, with no frozen target.

The existence manuscript's sparsification section supplies more than the main thin-tree statement. Its positive log-determinant normalization retains every subset rank; projected traces supply all undirected packing inequalities. Its two-system split controls both halves, including the cross blocks of the stacked matrix. Fairly choosing one of the two halves preserves each included edge's indicator in expectation. The algorithmic extraction section additionally has a continuous capacity ramp, separation and uncrossing to a chain of partitions, simultaneous shortcut response, and final extraction of a near-full packing. These are credited in combination, not replaced by a weaker literal reading.

The source first restricts to an extracted union B of q trees, however, and q is smaller than the original packing parameter r. Its final step also discards edges when selecting a tree. Fair choice of A or B minus A gives exactly half of 1_B in expectation, not half of 1_H. The rank frame certifies a large packing *contained in* a selected set, not an exact partition of all original edges into the prescribed number of bases. This distinction is the residual compatibility issue examined below; it is not a claim that such a compatibility theorem is impossible.

The source's log-determinant gradient already has a maximum-entropy interpretation. Independently, Chekuri–Vondrak–Zenklusen (CVZ), arXiv:0909.4348v2, Section 3, Theorem 1.1, Lemma 4.1 and Appendix B.1 provide exact-marginal swap rounding. For bases B1,B2 with masses beta1,beta2, symmetric basis exchange is randomized with probabilities beta1/(beta1+beta2) and beta2/(beta1+beta2); the weighted indicator is a martingale. Their product-moment argument and Chernoff tails are paid. Their cost-plus-packing proof in Section 6.2 uses tail bounds and Markov's inequality and allows loss in the cost; it does not assert an all-cut constant bound for every support tree.

Klein–Olver arXiv:2304.07674v1 was read through its actual alignment reduction and iterative-relaxation proof, not just its 22-thin headline. Theorem 2.7/4.6 preserves cost exactly for aligned laminar data; refining the matroid on tight rank sets is part of that operation. Theorem 2.8 first changes the point to x' <= eta x with eta>2; that is where exact marginal information is lost in the general reduction. Combining the two gives their Theorem 2.5, not (Q). Their conclusion asks a cost-preserving laminar question in that version. This is a historical statement about that body, not a determination of its status in 2026. A late check of Klein–Olver–Yeoh arXiv:2605.12669v1 read its theorem assembly and Appendix A alignment proof: its near-minimum-cut reduction uses a new dominated aligned point, and does not supply exact marginals for the original point. The polygon-cover proof was not read in full, and no novelty claim rests on that paper's absence of a statement.

## 3. The exact separating-cost condition

For fixed G,x,A, write Q_A=conv H_A(x), assuming it is nonempty. Then

    x in Q_A  iff  min_{T:1_T in H_A(x)} c(T) <= c.x
                    for every nonnegative c in R^E.           (1)

The forward implication is averaging. For the converse, if x is outside the compact convex polytope Q_A, finite-dimensional strict separation supplies a real vector d with d.x < min_{y in Q_A} d.y. Every vector in P(G), including x and every y in Q_A, has coordinate sum n-1. Choose M so d+M*1 >=0. Adding M(n-1) to both sides preserves the strict inequality, contradicting the displayed condition.

Thus exact marginal preservation is exactly a cost-factor-one statement for all nonnegative costs, with one fixed thin family. Merely identifying it as a convex-hull problem is not the remaining proof.

In contrast, the source implies a paid distribution with

    E[1_T] <= K x coordinatewise,       a_x(T) <= K always.    (2)

For rational x, let Q=Q_K. If Kx were not in Q+R_+^E, separation from this closed convex upper set would give a nonnegative c with c.Kx < min_{y in Q} c.y, contradicting the source. Hence some y in Q satisfies y<=Kx. A finite convex combination representing y is (2). The upper set is closed because Q is compact. For real x, use dyadic approximation in P(G), pass to a subsequence of distributions in the finite probability simplex, and pass the cut bounds and coordinate inequalities to the limit. Every tree of positive limiting probability occurs along a subsequence; there are finitely many cuts.

No extra multiplicative cost factor is lost in this convex separation. But y<=Kx is not y=x. The common total mass n-1 would make y<=x imply equality; it cannot remove K. Shifting a cost by M to make it nonnegative in the factor-K inequality introduces the extra term (K-1)M(n-1), so signed-cost translation does not repair this.

The aligned laminar primary has a positive consequence worth crediting: using (1) on its refined matroid, exact cost preservation implies a distribution with marginals x, all trees obeying the same laminar bounds 2 ceil(x(delta(S)))+1. This is a routine convex-separation consequence of that actual primary operation, not a new nominee. It neither covers all cuts nor preserves x through the unaligned scaling reduction.

## 4. Exact four-vertex separation, with a short proof

Take G=K4 on vertices 0,1,2,3, and order edges

    01, 02, 03, 12, 13, 23.

Let U={01,02,13}, V={03,12,23}, both spanning paths, and

    x=(1/5)1_U+(4/5)1_V=(1,1,4,4,1,4)/5.

There is a tree of thinness 15/13, namely V. No tree has smaller thinness, and the minimum A admitting an exact-x distribution is exactly 5/3.

Here is a proof independent of the enumeration. Denote a=01,b=02,c=03,d=12,e=13,f=23. The singleton cut masses at 0,1,2,3 are respectively 6/5,6/5,9/5,9/5. The two-two cut masses for 01|23, 02|13, 03|12 are respectively 2,13/5,7/5.

For thinness strictly below 5/3, vertices 0 and 1 must each have tree degree one, since degree two there has ratio 5/3. Vertices 2 and 3 can each have degree at most two, since degree three there has ratio 5/3. The degree sum is six, so the degrees are exactly (1,1,2,2). Thus the tree is a path with endpoints 0,1 and internal vertices 2,3. The two possibilities are {b,f,e} and {c,f,d}. The first crosses the cut 03|12 three times, ratio 15/7, and is excluded. Therefore the only tree below 5/3 is V={c,d,f}. Its maximum cut ratio is 15/13 at 02|13, from the cut list above. This proves the existence minimum.

Every distribution with marginals x must omit edge f with probability 1/5. A distribution supported only on V cannot do so. Hence A>=5/3. Conversely, the following three trees realize x:

    (1/5)1_{ {a,c,f} } + (1/5)1_{ {b,d,e} }
                           + (3/5)1_{ {c,d,f} } = x.          (3)

The seven cut ratios show that the first two trees have thinness 5/3 and the last has 15/13. This gives the matching upper bound.

Equivalently the single nonnegative cost c=1_{f} separates x from the convex hull of every thin family with A<5/3: all its trees cost one, while c.x=4/5. This small-scale separation does not refute a universal constant A, does not refute the source, and is not evidence of a nonroutine theorem by itself.

## 5. An all-parameter calculation and why local gluing does not amplify it

For a triangle with edges a,b,c, let 0<p<1/3 and x=(1-p,1-p,2p). Its only three trees have forced probabilities

    P({a,b})=1-2p,   P({a,c})=p,   P({b,c})=p.

Indeed each edge's omission probability is 1-x_e, so the decomposition is unique. The cut masses are 2(1-p),1+p,1+p. Consequently

    min_T a_x(T)=1/(1-p),
    min{A:x in conv H_A(x)}=2/(1+p).

The second divided by the first tends to two as p tends to zero. The single-tree optimum tends to one while exact marginals force positive mass on the other trees. This rules out identifying the two optimum values or preserving the optimum thinness at no loss. It supplies no obstruction to a universal constant at least two.

More generally, on any simple cycle C_l a fractional tree has coordinates x_i=1-p_i with p_i>=0 and sum p_i=1. Choosing the tree omitting edge i with probability p_i realizes x. A nontrivial cut has r>=2 cycle edges, so

    x(delta(S))=r-sum_{i in delta(S)}p_i >= r-1,
    |T intersect delta(S)| <= r <=2(r-1).

Every support tree is therefore 2-thin. This remains true when some p_i is zero or one. The triangle limit shows that no constant below two works uniformly even in this elementary family.

The same exact-marginal 2-thin conclusion holds for a finite connected simple cactus (each edge lies in at most one simple cycle). A spanning tree contains every bridge and omits exactly one edge from each cycle block. Marginals in P(G) restrict to these local distributions. Independently choose the omitted edge in each block with probabilities 1-x_e. For any cut, partition its edges into bridges and cycle blocks. On each block the preceding ratio is at most two (a cycle cut is either empty or has at least two edges); bridges contribute exactly their fractional mass. Summing proves the bound. This is elementary supporting feasibility, not a replacement target or nomination.

There is also an exact non-amplification statement. If G is obtained by joining connected graphs G1,G2 at a single vertex, P(G)=P(G1) times P(G2). Every spanning tree is the union of two spanning trees. For any fixed such tree,

    a_x(T) = max(a_{x1}(T1),a_{x2}(T2)).                      (4)

The upper bound follows by summing the two cut inequalities. To get the lower bound, extend a cut of one block to G by placing all other-block vertices on the same side as the shared vertex; it creates no edges of the other block. Restricting a distribution proves necessity of each block's decomposition threshold; taking the product of realizing distributions proves sufficiency. Thus both optimum values under one-vertex joining are maxima, not products. Repeating the triangle or K4 gadgets this way cannot create an unbounded obstruction.

## 6. Basis exchange, conditioning, and the source's symmetric split

**Full-support sampling is not a support bound.** On K_n, x_e=2/n belongs to P(K_n), and the uniform tree distribution has these marginals by symmetry and fixed tree size. Each star has positive probability. Its central singleton cut has ratio

    (n-1)/( (2/n)(n-1) ) = n/2.

Thus this exact-marginal maximum-entropy distribution does not itself have constant-thin support. This is not an obstruction to another distribution: symmetry can make conditioning on an invariant good event preserve uniform marginals. In general conditioning changes marginals; the K4 example proves an actual such failure below 5/3. A tail estimate alone neither produces nor forbids a marginal-preserving repair.

**Peeling a tree must preserve all base constraints.** For 0<t<1, subtracting tree vector b=1_T from x leaves a fractional tree

    z=(x-tb)/(1-t) in P(G)

only if, for every edge subset F with graphic rank r(F),

    t b(F) >= x(F)-(1-t)r(F),                              (5)

as well as x_e-tb_e>=0. This is just rearrangement of the rank inequalities. If x(F)=r(F), it forces b(F)=r(F). Hence support trees in an exact decomposition preserve every tight rank set of x; positive edge support alone is insufficient. For any tree in the minimal face, sufficiently small peeling is possible, but repeated peeling with only coordinate domination can drive the residual cut comparison up by the inverse remaining mass. That does not yield a uniform A.

For a concrete packing obstruction, K4 has a partition into the two paths U,V above, so it is a union of two trees. Extracting the star {01,02,03} gives one tree, but its complement is the triangle on 1,2,3 and an isolated vertex. Thus an arbitrary extracted tree is not removable as one part of a two-tree partition. This refutes the proposed universal extraction inference, not the possibility of choosing a suitable extracted tree. The source does not assert that every extraction has this extra property.

**What fair two-sided splitting does pay.** If H is the disjoint union of exactly q spanning trees, q even, and a partition H=A disjoint-union B gives each side exactly q/2 spanning trees, then fair choice of side sends the normalized multiplicity vector 1_H/q to 2*1_A/q or 2*1_B/q with exactly the same expectation. If both sides also satisfy

    |delta_A(S)|, |delta_B(S)| <= (1/2+epsilon_q)|delta_H(S)|,

the normalized cut comparison incurs factor 1+2epsilon_q. This is a compatible positive composition of symmetric choice and base partition, not a rejection of symmetric choice.

Suppose such exact base partitions existed for all sufficiently large dyadic q, with epsilon_q <= D q^(-eta), absolute D,eta>0, on every union of q trees. Recurse with fair choices down to a fixed dyadic q0. At q0, take any exact partition into q0 trees and choose one uniformly. Every original labelled edge then has probability 1/q. The final cut bound relative to 1_H/q is at most

    q0 product_{j>=1}(1+2D(2^j q0)^(-eta))
       <= q0 exp(2D q0^(-eta)/(2^eta-1)).                    (6)

This is independent of q and graph size. For x given by a dyadic convex combination of trees, realize that combination as labelled parallel copies of G; fair selection and projection give exact marginals x. For arbitrary x, approximate its finite convex coefficients dyadically and use compactness of the finite tree-distribution simplex. Every cut inequality passes to the limit. Thus the displayed exact bisection, if proved, would imply (Q).

**This bisection is not proved here.** The source's actual split keeps about half of an extracted packing, with summable loss; the two halves need not have the exact required cardinalities or jointly exhaust a base partition. Extraction's exceptional-edge loss precedes the fair split. The finite star example shows why one cannot replace this by an arbitrary tree-packing removal. Source uncrossing and primary basis exchange have been tried as compatible ingredients, but no cut-uniform exchange estimate repairing this loss was obtained.

A direct coordinate-frame repair also fails in its literal form. With m labelled edges, an isotropic frame in dimension m with exactly m columns has sum of squared norms m, so at least one norm is >=1; if the square frame is invertible all columns have norm one. It cannot simultaneously have the O(1/q) norm scale used by the small-vector split for q large. This only rejects adding a full independent coordinate frame and whitening it. It does not exclude randomized marginal preservation, lower-rank constraints, or another coupling. Fair choice before extraction needs no such coordinate frame at all.

## 7. Outcome and exact remaining obligation

The universal exact-marginal question is unresolved in this packet. No full theorem became proof-feasible enough to freeze. The work establishes the exact separating-cost formulation, credits the existing inflated-marginal consequence and aligned-laminar operation, derives concrete finite/all-parameter separations, proves the failure of one-vertex amplification, and isolates the exact base-partition requirement in a full bisection-to-distribution calculation.

To close this direction one needs a genuine uniform cost-factor-one selection among cut-thin trees, or an equivalent distribution construction. The exact bisection above is one sufficient route, not a conditional result being nominated. Conversely, to disprove the question one needs an unbounded family of separating-cost gaps; the cycle/K4 examples and their one-vertex joins do not provide it. Neither the general statement nor a current-open or priority claim follows from the bounded literature searches. Source geometry foundations not listed as read remain a coverage limit. No independent review or downstream formal/manuscript/release stage is requested.
