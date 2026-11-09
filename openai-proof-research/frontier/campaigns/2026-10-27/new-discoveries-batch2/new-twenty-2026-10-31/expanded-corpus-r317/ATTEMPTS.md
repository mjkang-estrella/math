# Ordinary mathematical attempts — zero credit

No mathematical program, solver, enumerator, or Lean process was run. The arguments below were reasoned on paper. None is an eligible new source-qualified endpoint.

## A. 373858: complete Brooks bridge

Let G be any finite simple claw-free graph of maximum degree at most three, and H its square: two distinct vertices are adjacent in H exactly when their G-distance is one or two. An ordinary seven-coloring of H is exactly a (2,2,2,2,2,2,2)-packing coloring of G, including disconnected G (infinite distance across components).

If d_G(v)<=2, then d_H(v)<=d_G(v)+2d_G(v)<=6. If d_G(v)=3, write its neighbors a,b,c. Claw-freeness forces an edge among a,b,c. There are at most six outgoing neighbor incidences besides those to v, and this edge consumes two of them inside N(v). Thus at most four distinct vertices at distance exactly two occur, and d_H(v)<=7. This count remains valid with repeated distance-two neighbors: repetitions only decrease the count.

There is no K8 component of H. A connected component of H has exactly the same vertices as its corresponding G-component, since G-edges are H-edges and H-edges never cross G-components. If such a component had eight vertices and were complete, each vertex would have H-degree seven, hence G-degree three. At each vertex its neighborhood must have exactly one edge: zero contradicts claw-freeness, and two or more consume at least four outgoing incidences and force H-degree at most five. Each vertex therefore belongs to exactly one triangle, because triangles through v are in bijection with edges in G[N(v)]. These triangles partition the eight vertices into triples, impossible since 3 does not divide 8.

Apply Brooks' theorem componentwise. A component of H with maximum degree <=6 has a greedy seven-coloring. A component of maximum degree seven is neither complete (K8 just excluded) nor an odd cycle (degree two), so Brooks gives seven colors. Reuse the same palette across components. Empty G is vacuous. Every hypothesis and exception in the classical theorem is discharged; no unresolved coloring bridge remains.

Dependency: Brooks' classical theorem, with actual statement/proof setup inspected in Baetz–Wood arXiv1401.8023v1 (report2001, posting2014). This is a complete classical reduction rather than an exclusion based on shortness. Latest2610.33803 has a different (1,2,2,2,2) endpoint; it was not misidentified as seven 2-packings. No new credit or Pi implementation is proposed.

## B. 371069: tensor semantics, complete refutation and exact value

Use the usual tensor/direct product adjacency (u,v)~(u',v') iff u~u' in S_m and v~v' in S_n. Write each star as a center plus its leaves. The central pair is adjacent exactly to all mn leaf-leaf pairs. The m leaf-center pairs are adjacent to all n center-leaf pairs. There are no other edges. Thus the graph is K_(1,mn) disjoint union K_(m,n), for m,n>=1.

A complete bipartite component in a proper coloring with a global palette of k>=3 colors can witness at most one b-color. Indeed, if b-vertices occur on opposite sides, let their colors be alpha,beta. Every vertex of color other than alpha must lie on the opposite side from an alpha b-vertex if it is to be seen there. In particular any color gamma different from alpha,beta must occur on that side. The beta b-vertex similarly forces gamma on the first side. Properness of the complete bipartite graph forbids the same color on both sides. Hence no b-vertices on opposite sides. On the same side, a b-vertex of color alpha cannot see any different color beta appearing on its own side, since beta cannot occur on the opposite side. Thus all b-vertices in that component have one color.

There are only two components, so at most two colors can have b-witnesses if k>=3, contradicting the k b-color requirement. Both components have edges and a common two-color bipartition gives b-witnesses for both colors. Consequently b(S_m x S_n)=2 for all positive m,n, not m+n+1.

For the exact negative endpoint a still more direct source bridge suffices: take distinct stars S3,S4 (both safely above tiny-parameter conventions). Degrees are 12 at the central pair, four at each of three leaf-center pairs, three at each of four center-leaf pairs, and one at each of twelve leaf-leaf pairs. A proposed eight-color b-coloring requires eight different vertices of degree at least seven, while only one exists. This is precisely source Proposition2.1's m-degree bound, with all degree/cardinality bridges explicit. No enumeration was performed.

Scope warning: the paper declares connected graphs globally and gives no tensor adjacency definition; tensor products here are disconnected. An intended restriction to connected products makes the quantifier vacuous; an alternative intended operator is unidentified. Its square-of-Cartesian-product theorem already has m+n+1 for unequal stars, so changing operators would merely restate a source theorem. This is a complete standard-semantic/source-bound correction, not a qualifying significant new solution. No Pi plan.

## C. 375797: exact known-star domain correction

For X=K_(1,3), put the center first in the adjacency matrix A. Direct block multiplication gives A^3=3A. With theta=sqrt(3)t, the exponential is I + i sin(theta) A/sqrt(3) + (cos(theta)-1) A^2/3 (the power series separates even/odd terms). At t=2pi/(3sqrt(3)), cos(theta)=-1/2 and sin(theta)=sqrt(3)/2. Thus U(t)=exp(itA) has center-center entry -1/2; all center-leaf and leaf-center entries i/2; all leaf diagonal entries 1/2; and all distinct leaf-leaf entries -1/2. Every entry has squared modulus 1/4: uniform mixing holds exactly.

If exp(it) were a root of unity, there would be integers k>0 and ell with kt=2pi ell, hence k=3sqrt(3)ell. Ell cannot be zero, and this would make sqrt(3) rational. The standard proof that sqrt(3) is irrational (lowest-term fraction, then divisibility of numerator and denominator by3) excludes it. The literal all-graph root-of-unity assertion is false.

The spectrum here is 0,0,sqrt(3),-sqrt(3), so this does not refute an integral-spectrum version. The star is a public known mixing example (Godsil source explicitly lists it). This is a complete classical/domain bridge, not a new graph or an eligible endpoint. No floating-point exponential, symbolic solver, or Lean was used.

## D. 367545: sustained fixed-length reconstruction, then public predecessor

Theorem23 says each member of a minimal presentation is a cyclic flat; its proof body was read. For a presentation of fixed length k define f(S)=#{i : S is not contained in X_i}. The source rank formula is r(S)=min_(A<=S)(f(A)+dim(S)-dim(A)). For any cyclic subspace C, f(C)=r(C). To prove this, choose a minimizer A. If A<C, take a hyperplane H of C containing A; the same rank formula gives r(H)<=r(C)-1. But C is spanned by its circuits, so some circuit D<=C is not contained in H. Then D intersect H is a proper hyperplane of the circuit D, hence independent and of rank dim(D)-1=r(D). Submodularity gives r(C)=r(H+D)<=r(H)+r(D)-r(H intersect D)=r(H), a contradiction. Thus A=C.

For every cyclic flat F the number of presentation members containing F is k-r(F). Since every X_i is a cyclic flat, their multiplicities are recovered uniquely by descending induction over the finite poset of cyclic flats: mult(F)=k-r(F)-sum_(cyclic flats E>F) mult(E). Hence two minimal presentations of the same fixed length are equal as multisets, and can differ only by reindexing. This supplies the missing recovery step; merely saying each X_i is cyclic would not prove uniqueness.

If presentation length is not fixed, literal uniqueness is false: on a one-dimensional space V, both the one-member family (0) and the two-member family (0,0) yield the free rank-one q-matroid, and both are coordinatewise minimal because 0 has no proper subspace. This is a presentation-length/domain correction only. No claim to refute the intended rank-sized statement is made.

A dated public predecessor was found: Relinde Jurrius, joint work with Gianira Alfarano, The Matroid Union, 2025-11-03, “Presentations of avoiding transversal (q-)matroids”, https://matroidunion.org/?p=5911. Its entire mathematical body, six-element example, and explicit rank-sized convention were read. It expressly states the same unique-minimal-presentation conclusion and sketches the cyclic-core proof. Its q-PropositionB step is described rather than written in full; that limitation is retained. Our fixed-length proof is not claimed as new-to-literature in the presence of that public theorem/argument.

## E. 374167: why the tempting projection route stops

For P=A2, induced-P-free means a chain. Saturated means the chain is inclusion-maximal; it must include both extrema and increase exactly one coordinate by one at every step, since an omitted extremum or intermediate cover could be added. Therefore every such chain has n(t-1)+1 elements. This proves monotonicity for A2. For P=C2 a singleton least element is saturated, so sat*=1. These special cases furnish no new full-scope endpoint.

For general P, dropping a coordinate preserves order but can collapse an incomparable pair into a comparable pair (e.g. (1,2),(2,1) after deleting the second coordinate). It can also identify distinct elements. Source Lemma2.14 resolves projection only for a non-separating coordinate; general extremal families can have every coordinate separating. Similarly restriction to one coordinate slab need not remain saturated: witnesses for an omitted point can use points outside the slab. No repair proving the needed uniform compression was found. This route remains genuinely incomplete; it is not excluded by the separate published dichotomy result.
