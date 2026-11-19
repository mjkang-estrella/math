# Two cliques joined by a path refute the line–middle conjecture for outer-connected domination

## Abstract

Let \(G_h\) consist of two copies of \(K_{2h}\) joined by a three-edge path with fresh internal vertices, where \(h\ge 2\). Its middle graph has outer-connected domination number \(2h+2\), and its line graph has outer-connected domination number \(\binom{2h}{2}+h+1\). Both values hold under either convention for connectivity of the empty graph. The strict reverse inequality disproves Conjecture 7.6 of Kazemnejad, Pahlavsay, Palezzato and Torielli at infinitely many orders. A Lean 4 verification proves the refutation with explicit uniform bounds.

## Source statement and definitions

Conjecture 7.6 of [1] reads as follows.

> Let \(G\) be a graph of order \(n\geq 2\). Then  
> \(\widetilde{\gamma}_c(L(G))\leq\widetilde{\gamma}_c(M(G))\).

There is no connectedness hypothesis in the conjecture. Section 1 of [1] assumes throughout that every graph is non-empty, finite, undirected and simple. The same inequality is the assertion of MathDB record 355218 [2]. The counterexamples below are connected and have edges, so they meet this standing assumption under any reading of non-empty.

All graphs considered here are finite, undirected and simple. A set \(D\subseteq V(H)\) dominates \(H\) if every vertex in \(V(H)\setminus D\) has a neighbor in \(D\). This is equivalent to the closed-neighborhood definition in [1], since a vertex of \(D\) already belongs to its own closed neighborhood. In Definition 1.2 of [1], an outer-connected dominating set is a dominating set whose complement induces a connected graph, and the outer-connected domination number \(\widetilde{\gamma}_c(H)\), abbreviated \(\operatorname{ocd}(H)\), is the least size of such a set. We treat both conventions for the empty complement. Under the convention that admits it, connectivity means that every pair of vertices of the complement is joined by a walk. Under the nonempty convention it also requires a vertex in the complement. The witness sets below have nonempty complements, and all lower bounds apply to any admissible set in either convention.

The vertices of \(L(G)\) are the edges of \(G\). Two distinct edge-vertices are adjacent precisely when their edges share an endpoint. In Definition 1.3 of [1], the middle graph \(M(G)\) has the disjoint union of the original vertices and the edge-vertices. Its edge-vertices induce \(L(G)\). Across the two vertex types, an original vertex is adjacent precisely to the edges incident with it. The original vertices form an independent set.

## Previous results

For trees, Corollary 4.6 of [1] gives a strict inequality in the conjectured direction. Proposition 7.2 does the same for cycles of order at least three, using the isomorphism \(L(C_n)\cong C_n\), Cyman's value \(\operatorname{ocd}(C_n)=n-2\) [3], and the middle-graph value of Theorem 4.10. Proposition 7.3 treats wheels of order at least five by constructing outer-connected dominating sets in their line graphs and using the middle-graph value from Theorem 4.11. Proposition 7.4 gives equality on \(W_4=K_4\). The equality-classification question in Problem 7.5 is separate from Conjecture 7.6. Conjecture 7.1 of [1], which asserts \(\operatorname{ocd}(G)<\operatorname{ocd}(M(G))\) for graphs of order at least two, is a different comparison and is not addressed here. Theorem 4.1 bounds \(\operatorname{ocd}(M(G))\) above by the order of a connected graph \(G\) of order at least two, by selecting all original vertices of \(M(G)\). The complement in that construction consists of edge-vertices. Here we need a smaller middle-graph set and a line-graph bound that uses the path separators.

## Theorem

**Theorem.** For every integer \(h\ge 2\), let \(G_h\) consist of two disjoint complete graphs \(A,B\), each of order \(2h\), with a path \(a,x,y,b\) added, where \(a\in V(A)\), \(b\in V(B)\), and \(x,y\) are new vertices. There are no other edges between these parts. Then \(G_h\) is connected and has order \(4h+2\). Under either convention for connectivity of the empty complement,
\[
\operatorname{ocd}(M(G_h))=2h+2
\;<\;
\operatorname{ocd}(L(G_h))=\binom{2h}{2}+h+1.
\]
In particular, the universal assertion that for all integers \(n\ge 2\) and all simple graphs \(G\) on \(\{0,\ldots,n-1\}\) one has \(\operatorname{ocd}(L(G))\le\operatorname{ocd}(M(G))\) is false under both conventions. It fails on a connected graph for each order \(4h+2\) with \(h\ge 2\). In Lean we prove the following uniform inequalities sufficient for these conclusions:
\[
\operatorname{ocd}(M(G_h))\le 2h+2 < \binom{2h}{2}+1
\le \operatorname{ocd}(L(G_h)).
\]

## Proof

Write \(t=2h\), \(c=\binom t2=h(2h-1)\), and \(e_1=ax,\ e_2=xy,\ e_3=yb\). We use the name of an edge for the corresponding edge-vertex when working in \(L(G_h)\) or \(M(G_h)\). The two cliques each have \(c\) edges by the bijection with unordered pairs of their \(t\) vertices. The cliques and the path are connected and share the endpoints \(a,b\) as specified, so \(G_h\) is connected. It has \(2t+2=4h+2\) vertices.

### Separators and residual connectivity

Removing any \(e_i\) from \(G_h\) partitions the vertices into two sides, one containing \(A\) and one containing \(B\), because the only edges outside the cliques belong to the path. Each surviving edge has both endpoints on one side. When the edge-vertex \(e_i\) is deleted from \(L(G_h)\) or \(M(G_h)\), assign each surviving edge-vertex its endpoint side and each surviving original vertex its own side. Adjacent edge-vertices share a common endpoint and hence have the same side. An adjacent original vertex and edge-vertex have the same side by incidence, and original vertices have no mutual adjacency in \(M(G_h)\). Thus every walk that avoids \(e_i\) stays on one side. In either graph, a connected complement containing an edge-vertex from each clique must therefore contain all three path edge-vertices. The closed neighborhood of \(e_2\) in \(L(G_h)\) is exactly \(\{e_1,e_2,e_3\}\), since \(x\) and \(y\) have no other incident edges in \(G_h\).

In either clique, label vertices by \(0,\ldots,t-1\) and select the \(h\) disjoint edges with endpoint labels \(2j,2j+1\), for \(0\le j<h\). This is a perfect matching, since each label has one of these two forms for a unique \(j\). The residual clique after deleting its matching edges is connected. Vertices from different matched pairs are adjacent. Distinct vertices in the same pair can be joined through a vertex in a different pair, which exists by \(h\ge 2\). Every original clique vertex is incident with a residual edge by the same choice of a different pair. With both matchings deleted and the path retained, the residual graph on the original vertices of \(G_h\) is connected: every vertex of a clique reaches its path endpoint and the path joins the endpoints and the two internal vertices.

The line graph of any connected graph with at least one edge is connected. Given two edges, choose one endpoint of each and take a walk between those endpoints in the connected graph. Place the two chosen edges before and after the list of walk edges, in that order. Consecutive edges share an endpoint, including when the walk has length zero. Removing adjacent repetitions yields a walk in the line graph between the chosen edge-vertices, or the zero-length walk if they coincide. The existence of an edge gives the required nonemptiness.

### The middle graph

For the upper bound, select the two matchings as edge-vertices and select the original vertices \(x,y\). All selections are distinct and there are \(2h+2\) of them. Each original clique vertex has its matching edge as a selected neighbor. Each unselected clique edge shares an endpoint with a selected matching edge, and the two edge-vertices are distinct because the former is unselected. Each path edge contains \(x\) or \(y\) and so has a selected original neighbor. This exhausts all unselected vertices, proving domination. The unselected edge-vertices induce the line graph of the residual graph with both matchings deleted and the path intact, which is connected by the preceding arguments. The remaining original vertices are exactly the clique vertices, each incident with an unselected clique edge. Paths through these incident edges join any two vertices of the complement. The complement contains \(e_2\), so the set is admissible under both conventions.

For the lower bound suppose an outer-connected dominating set \(D\) has \(|D|\le 2h+1\). Since \(h\ge 2\), \(c=h(2h-1)\ge 3h\ge 2h+2\). Each clique has an edge-vertex outside \(D\), so all three path edge-vertices are outside \(D\) by the separators. The only neighbors of \(x\) in \(M(G_h)\) are \(e_1,e_2\), and the only neighbors of \(y\) are \(e_2,e_3\). Domination therefore forces the original vertices \(x,y\) themselves into \(D\). Every original clique vertex must either belong to \(D\) or be incident with a selected edge. The selected original clique vertices cover only themselves in this count, since original vertices are independent. Selected clique edge-vertices cover two original vertices apiece. The selected \(x,y\) cover no original clique vertex, and all path edge-vertices are outside \(D\). Hence the union of the covered original clique vertices has size at most \(2(|D|-2)\), but it must have size \(4h\). This gives \(|D|\ge 2h+2\), a contradiction.

### The line graph

Let \(D\) be any outer-connected dominating set of \(L(G_h)\). To dominate \(e_2\) in the closed-neighborhood sense, \(D\) must contain at least one of \(e_1,e_2,e_3\). If an edge-vertex from each clique were outside \(D\), the separator argument would then contradict connectivity of the complement. Thus \(D\) contains the entire edge set of one clique, say \(A\), after interchanging the names and reversing the path if necessary. The path edge already counted is distinct from these clique edges, so \(|D|\ge c+1\). This is the lower bound used in Lean. To see that a minimum exists even with the nonempty convention, all line-graph vertices except \(e_2\) form an admissible set: \(e_2\) has the selected neighbor \(e_1\) and the complement is a singleton.

We now sharpen the lower bound. If \(D\) contains every edge of \(B\) too, then \(|D|\ge 2c\ge c+h+1\), since \(c\ge 3h\) and \(h\ge 2\). Otherwise an edge-vertex of \(B\) remains in the complement. If \(e_3\) is selected, then \(e_1,e_2\) must both be selected as well, as each would otherwise be separated from that residual \(B\)-edge by \(e_3\). Let \(j\) be the number of selected \(B\)-edges. Every pair of distinct vertices in \(B\) gives a \(B\)-edge. If two such vertices are outside \(\{b\}\) and both are incident with no selected \(B\)-edge, their edge is unselected and shares no endpoint with a selected edge. In fact, selected \(A\)-edges have neither endpoint in \(B\), and the only path edge meeting \(B\) is \(e_3\), at \(b\). This would leave the edge undominated. Therefore all but at most one of the \(t\) vertices of \(B\) are covered by the endpoints of the \(j\) selected \(B\)-edges together with \(b\). Consequently \(2j+1\ge t-1=2h-1\). Thus \(j\ge h-1\), and the \(c\) clique edges in \(A\) and three path edges give \(|D|\ge c+3+h-1=c+h+2\).

If \(e_3\) is unselected, no selected edge outside \(B\) is incident with a vertex of \(B\). Two vertices of \(B\) incident with no selected \(B\)-edge would again have their connecting edge undominated. Thus \(2j\ge t-1=2h-1\), which gives \(j\ge h\) because \(j\) is an integer. Counting one selected path edge along with the clique edges gives \(|D|\ge c+h+1\).

For the upper bound select every \(A\)-edge, \(e_1\), and a perfect matching of \(B\). The selected sets are disjoint, giving size \(c+h+1\). For any unselected \(B\)-edge, the matching edge at either endpoint dominates it. The matching edge at \(b\) dominates \(e_3\). The selected \(e_1\) dominates \(e_2\) by their common endpoint \(x\). The unselected \(B\)-edges induce the connected line graph of the residual clique. There is a residual \(B\)-edge at \(b\), so \(e_3\) joins this connected subgraph and \(e_2\) joins through \(e_3\). This proves connectivity of the complement, which contains \(e_2\). The line-graph minimum is therefore \(c+h+1\) under both conventions.

Finally \(c+1\ge 3h+1 > 2h+2\), since \(h\ge 2\). This proves the weaker explicit bounds and the strict inequality between the exact values. Transporting a graph along a bijection of its vertex set induces bijections on unordered edges and on the disjoint union of vertices and edges. These preserve the incidences and hence the adjacencies in the line and middle graphs in both directions. In either transformed graph a bijection preserving adjacency in both directions maps dominating sets to dominating sets, maps complement walks to complement walks, and preserves cardinalities and nonemptiness. Thus labeling \(G_h\) by \(\{0,\ldots,4h+1\}\) preserves the inequalities. Taking \(h=2\) gives a counterexample with \(n=10\), and the orders \(4h+2\) strictly increase for \(h=2,3,\ldots\). \(\square\)

## Lean correspondence

The Lean source defines line-graph vertices literally as the edge-set subtype of a Mathlib simple graph. Middle-graph vertices are the sum of the original vertex type and this subtype. For the empty-complement convention the induced remainder must be preconnected. For the nonempty convention it must also have a vertex, as shown by the equivalence with Mathlib connectedness. The natural-number infimum is a minimum when an admissible set exists. For an empty family of admissible sets, its Lean value is zero by the natural-number infimum convention. The witnesses have admissible sets in both graphs under both connectivity conventions, so the fallback has no effect on the refutations.

| Mathematical step | Lean declaration in namespace OuterDom, with CP denoting CliquePath |
| --- | --- |
| Operators and minimum | lineGraph, middleGraph, Remainder, IsOCDS, isOCDS_false_iff, ocd, ocd_le, ocd_attained |
| Clique/path graph, complete edge embedding, and path edges | CP.graph, CP.cliqueEdge, CP.bridge, CP.cliqueEdge_ne_bridge |
| Same-side label away from a removed bridge | CP.cutSide, CP.crossing_edge, CP.edge_side_eq |
| Constancy along walks in the line remainder and clique forced into the selected set | label_eq_of_reachable, CP.separated_by_bridge, CP.entire_clique_selected |
| Central path edge \(e_2\) dominated only by path edges, singleton-complement line-graph witness, and lower bound | CP.incident_joint, CP.has_selected_bridge, CP.center_adj_left, exists_ocds_of_adj, CP.line_card_lower, CP.line_lower |
| Perfect matchings and domination in the middle graph | CP.matchingEdge, CP.matching_covers, CP.matchingSet_dominates |
| Residual graph connectivity and original graph connectivity | CP.residual_clique_adj, CP.residual_clique_reaches_root, CP.residual_connected, CP.graph_connected |
| Passing a walk to a walk of incident edges and attaching original vertices | incident_reachable, line_preconnected, CP.toMiddleRemainder, CP.reaches_residual_edge |
| Upper bound and strict comparison of the bounds | CP.middle_upper, CP.middle_bound_lt_line_bound, CP.clique_path_bounds |
| Relabeling, invariance, and labeled bounds | CP.labels, CP.labelingIso, lineIso, middleIso, ocds_map, ocd_iso, CP.labeled_clique_path_bounds |
| Strict family, infinitely many orders, and both quantified refutations | CP.clique_path_strict, CP.infinitely_many_counterexample_orders, not_conjecture76, mathdb_355218, mathdb_355218_nonempty |

The proof of the line-graph bound in Lean begins with the forced choice of a path edge and labels the remaining edges by a side of that cut. The proof of the middle-graph upper bound uses explicit indices \(0\) and \(2\) in different matched pairs to supply residual neighbors and paths to each clique's attachment point. It factors the edge-to-edge walk argument through the line graph of the residual graph. The paper also proves exact values. The middle-graph counting lower bound, the sharpened line-graph lower bound, and the matching-based line-graph upper bound are written arguments only.

~~~lean
OuterDom.Conjecture76 (a : Bool) : Prop
OuterDom.not_conjecture76 (a : Bool) : ¬OuterDom.Conjecture76 a
OuterDom.mathdb_355218 :
  ¬∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      2 ≤ n → OuterDom.ocd true (OuterDom.lineGraph G) ≤ OuterDom.ocd true (OuterDom.middleGraph G)
OuterDom.mathdb_355218_nonempty :
  ¬∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      2 ≤ n → OuterDom.ocd false (OuterDom.lineGraph G) ≤ OuterDom.ocd false (OuterDom.middleGraph G)
OuterDom.CliquePath.clique_path_bounds {h : ℕ} (hh : 2 ≤ h) (a : Bool) :
  OuterDom.ocd a (OuterDom.middleGraph (OuterDom.CliquePath.graph h)) ≤ 2 * h + 2 ∧
    2 * h + 2 < (2 * h).choose 2 + 1 ∧
      (2 * h).choose 2 + 1 ≤ OuterDom.ocd a (OuterDom.lineGraph (OuterDom.CliquePath.graph h))
OuterDom.CliquePath.labeled_clique_path_bounds {h : ℕ} (hh : 2 ≤ h) :
  (OuterDom.CliquePath.labeledGraph h).Connected ∧
    ∀ (a : Bool),
      OuterDom.ocd a (OuterDom.middleGraph (OuterDom.CliquePath.labeledGraph h)) ≤ 2 * h + 2 ∧
        2 * h + 2 < (2 * h).choose 2 + 1 ∧
          (2 * h).choose 2 + 1 ≤ OuterDom.ocd a (OuterDom.lineGraph (OuterDom.CliquePath.labeledGraph h))
OuterDom.CliquePath.clique_path_strict {h : ℕ} (hh : 2 ≤ h) (a : Bool) :
  OuterDom.ocd a (OuterDom.middleGraph (OuterDom.CliquePath.labeledGraph h)) <
    OuterDom.ocd a (OuterDom.lineGraph (OuterDom.CliquePath.labeledGraph h))
OuterDom.CliquePath.infinitely_many_counterexample_orders (a : Bool) :
  {n |
      ∃ G,
        2 ≤ n ∧ G.Connected ∧ OuterDom.ocd a (OuterDom.middleGraph G) < OuterDom.ocd a (OuterDom.lineGraph G)}.Infinite
'OuterDom.not_conjecture76' depends on axioms: [propext, Classical.choice, Quot.sound]
'OuterDom.mathdb_355218' depends on axioms: [propext, Classical.choice, Quot.sound]
'OuterDom.mathdb_355218_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
'OuterDom.CliquePath.clique_path_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'OuterDom.CliquePath.labeled_clique_path_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'OuterDom.CliquePath.clique_path_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
'OuterDom.CliquePath.infinitely_many_counterexample_orders' depends on axioms: [propext, Classical.choice, Quot.sound]
~~~

## Scope and limits

The supplied discovery and independent review conducted a bounded prior-art search covering the source preprint, its citing paper on total outer-connected domination [4], and title, abstract or snippet searches for later work. No prior resolution appeared in the material searched. The journal versions of [1] and [4] and the full texts of the related work on exact double domination and paired disjunctive domination were outside the material verified here. The supplied reviewer also checked both numbers by exhaustive enumeration at \(h=2,3\). Neither the written proof nor the Lean proof relies on enumeration. The review was model-generated. This manuscript and formalization were AI-produced and have had no human peer review.

## References

[1] Farshad Kazemnejad, Behnaz Pahlavsay, Elisa Palezzato, and Michele Torielli. *Connected and outer-connected domination number of middle graphs*. arXiv:2206.15439v1, 2022. [Preprint](https://arxiv.org/abs/2206.15439).

[2] MathDB. *Line-middle graph inequality conjecture for outer-connected domination*. Record 355218. [Record](https://mathdb.com/p/355218/line-middle-graph-inequality-conjecture-for-outer-connected).

[3] J. Cyman. *The outer-connected domination number of a graph*. Australasian Journal of Combinatorics 38 (2007), 35–46.

[4] Farshad Kazemnejad, Behnaz Pahlavsay, Elisa Palezzato, and Michele Torielli. *Total outer-connected domination number of middle graphs*. arXiv:2308.02127, 2023. [Preprint](https://arxiv.org/abs/2308.02127).
