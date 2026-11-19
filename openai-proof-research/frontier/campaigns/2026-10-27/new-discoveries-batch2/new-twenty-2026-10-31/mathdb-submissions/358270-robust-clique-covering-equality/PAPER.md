# Equality in the lower bound for the robust clique covering number

## Abstract

A finite simple graph has equal clique covering and 1-robust clique covering numbers exactly when it is edgeless. For a graph with an edge \(xy\), we isolate \(x\) and delete those edges at \(y\) whose other endpoints are distinct from \(x\) and fail to neighbor \(x\). Every clique partition after deletion can then be made one part smaller in the original graph. This proves Conjecture 1 of Bacsó, Patkós, Tuza and Vizer.

## Source statement and definitions

Conjecture 1 in §3.2.1 of [1] reads, “The lower bound \(\theta_1\geq\theta\) is not tight, except for edgeless graphs.”

All graphs are finite and simple. A clique is a set in which all distinct pairs are adjacent. The clique covering number \(\theta(G)\) is the least number of cliques whose union is \(V(G)\). Equivalently, it is the least \(k\) admitting a map \(V(G)\to\{0,\ldots,k-1\}\) whose distinct equal-colored vertices are adjacent. Given \(k\) covering cliques, assign each vertex to the first covering clique containing it. Each resulting fiber is a subset of that clique. Conversely, the nonempty fibers of a valid map are at most \(k\) cliques and cover the vertices. These arguments also apply to zero vertices, with zero colors.

In Definition 1(i) of [1], a 1-selection is a map \(f:V(G)\to E(G)\cup\{\varnothing\}\) such that if \(f(v)\ne\varnothing\), then \(v\in f(v)\). Choices may coincide. An isolated vertex has only the empty choice, and any vertex may make the empty choice. The graph \(G_f\) retains all vertices and deletes the chosen edges. Definition 2 gives \(\theta_1(G)=\max_f\theta(G_f)\) over all 1-selections. The maximum exists because the selection set is finite and includes the everywhere-empty map. The MathDB record [2] phrases the conjecture for isolate-free graphs, in which every vertex has a neighbor.

## Previous results

Proposition 4 of [1] gives \(\theta\leq\theta_1\leq 3\theta\) for isolate-free graphs. Proposition 5 studies criticality of hypothetical equality cases by deleting a full star. Theorem 6 shows that every edge in an equality case must lie in at least two triangles. For an edge in at most one triangle, the union of the two full stars is quasi-unicyclic, and the proof deletes it by a 1-selection. The following explicit selection is our gloss and is not written out in [1]. With no triangle, root the star union at one endpoint and let each nonroot vertex select its edge to its parent. With one triangle, let each triangle vertex select the next edge around the cycle and each other incident vertex select its edge toward the triangle. After deletion the two endpoints become singleton parts, which can be merged across their original edge. Proposition 7 of [1] likewise deletes the full star at one vertex together with one further edge. The proof below modifies these arguments of [1]: it keeps the isolation of one endpoint and replaces the second full star by a partial star at the second endpoint. The clique containing that endpoint can then be merged with the first endpoint's singleton.

## Theorem and proof

**Theorem.** For every finite simple graph \(G\), \(\theta_1(G)=\theta(G)\) if and only if \(G\) has no edges. More precisely, for every ordered adjacent pair \(x,y\) in \(G\), there exists a 1-selection \(f\) with \(\theta(G_f)\geq\theta(G)+1\). In particular, \(\theta(G)<\theta_1(G)\) for every finite simple graph with an edge, and the equality characterization holds for every finite isolate-free simple graph. The same equality characterization holds if the maximum defining \(\theta_1\) ranges only over selections making a choice at each nonisolated vertex.

**Proof.** Fix an ordered adjacent pair \(x,y\). A vertex \(z\) adjacent to \(x\) selects \(zx\). A vertex \(z\ne x\) that is not adjacent to \(x\) and is adjacent to \(y\) selects \(zy\). Every other vertex chooses nothing. Each chosen edge exists by the relevant adjacency condition, contains \(z\), and is the only choice made by \(z\) because the two conditions are disjoint. Every edge at \(x\) is chosen by its other endpoint. Further, if \(zy\) survives and \(z\ne x\), then \(z\) is adjacent to \(x\), since otherwise \(z\) would choose \(zy\).

Take a cover map of \(G_f\) using \(k=\theta(G_f)\) colors. A cover map exists with \(|V(G)|\) colors by assigning distinct colors, so the least possible number is attained. The color class of \(x\) equals \(\{x\}\), since a distinct vertex of its color would be adjacent to \(x\) in \(G_f\). Thus \(y\ne x\) has a different color. Every vertex of the class of \(y\) is adjacent to \(x\) in \(G\). For \(y\) this follows from the chosen adjacency. For a different vertex \(z\) of that class, \(z\ne x\) and \(zy\) survives by the cover condition, so the preceding deletion property applies. The class of \(y\) is also a clique in \(G\) because deletion only removes edges. Reassign \(x\) to the color of \(y\). Pairs involving \(x\) in the enlarged class are adjacent by the property just proved, and the other equal-colored pairs retain their old adjacency. This leaves the former color of \(x\) unused. Its deletion leaves \(k-1\) available colors, which can be relabeled in order. Since the color of \(x\) existed, \(k\ge 1\). Therefore \(\theta(G)\leq k-1\), or \(\theta(G_f)\geq\theta(G)+1\).

By the maximum definition, any edge gives \(\theta_1(G)\geq\theta(G)+1\). If \(G\) is edgeless, each choice is empty and \(G_f=G\) for every selection. This proves both implications and the strict inequality, including the restriction to isolate-free graphs.

Finally, any allowed selection can be completed by choosing an arbitrary incident edge at each nonisolated vertex that chose nothing. Completion preserves all previously selected edges, so the new surviving graph is a subgraph on the same vertices. A clique cover of that subgraph is a clique cover of the old surviving graph, so completion weakly increases \(\theta\) after deletion. Completing a maximizing selection shows that the restricted maximum is at least the unrestricted maximum. The opposite inequality follows because every completed selection is a source selection. \(\square\)

## Lean correspondence

| Step | Declaration in namespace RobustCover |
| --- | --- |
| Optional incident edge and deletion | OneSelection, OneSelection.removed |
| Cover by a map into a finite color type, minimum and maximum | HasCliqueCover, theta, theta1 |
| Existence of a cover and attainment of the minimum | singleton_cover, cover_theta |
| Attainment of the maximum and lower bound | theta1_attained, deletion_le_theta1, theta_le_theta1 |
| Two selection rules and their deletion consequences | orderedSelection, ordered_isolates, ordered_retains_compatible |
| Move the singleton into the class of the second endpoint | exists_selection_increase |
| Equality, strict source proposition, and isolate-free specialization | robust_theta_strict, Conjecture1, conjecture1, mathdb_358270 |
| Completion and agreement with compulsory choices | completeSelection, complete_selects, complete_removed_le, theta_mono, theta1Required_eq, robust_theta_required_strict |

Lean follows the color-map proof above, using a finite-type equivalence to relabel the remaining colors. The discovery proof merges the parts as sets. The manuscript includes the translation from overlapping covers to color maps, while Lean starts with the requested map definition. Lean uses a natural-number infimum and supremum, with attainment justified by nonemptiness and, for the supremum, the upper bound \(|V(G)|\). The proposition `Conjecture1` is defined as `∀ {W : Type} [Fintype W] (G : SimpleGraph W), G ≠ ⊥ → theta G < theta1 G`. The isolate-free hypothesis `_hiso` of `mathdb_358270` is not used in its proof.

~~~lean
RobustCover.theta1_attained {V : Type} [Fintype V] (G : SimpleGraph V) :
  ∃ s, RobustCover.theta s.removed = RobustCover.theta1 G
RobustCover.theta1Required_eq {V : Type} [Fintype V] (G : SimpleGraph V) :
  RobustCover.theta1Required G = RobustCover.theta1 G
RobustCover.robust_theta_required_strict {V : Type} [Fintype V] (G : SimpleGraph V) :
  RobustCover.theta1Required G = RobustCover.theta G ↔ G = ⊥
RobustCover.exists_selection_increase {V : Type} [Fintype V] (G : SimpleGraph V) {x y : V} (h : G.Adj x y) :
  ∃ s, RobustCover.theta G + 1 ≤ RobustCover.theta s.removed
RobustCover.robust_theta_strict {V : Type} [Fintype V] (G : SimpleGraph V) :
  RobustCover.theta1 G = RobustCover.theta G ↔ G = ⊥
RobustCover.Conjecture1 : Prop
RobustCover.conjecture1 : RobustCover.Conjecture1
RobustCover.mathdb_358270 {V : Type} [Fintype V] (G : SimpleGraph V) (_hiso : ∀ (v : V), ∃ w, G.Adj v w) :
  RobustCover.theta1 G = RobustCover.theta G ↔ G = ⊥
'RobustCover.theta1_attained' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustCover.theta1Required_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustCover.robust_theta_required_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustCover.exists_selection_increase' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustCover.robust_theta_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustCover.conjecture1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobustCover.mathdb_358270' depends on axioms: [propext, Classical.choice, Quot.sound]
~~~

## Scope and limits

The bounded prior-art assessment uses the supplied discovery and independent review. Those searches covered the source arXiv text, the companion arXiv preprint 2305.01927, the planar robust-coloring preprint 2401.08324, and titles or snippets of later citing work. The full Graphs and Combinatorics version of [1], the journal versions of the follow-ups, and the full texts of the two 2026 non-arXiv citing papers were outside the material verified here. A resolution in unexamined literature remains possible. The independent review is model-generated. This manuscript and formalization were AI-produced and have had no human peer review.

## References

[1] Gábor Bacsó, Balázs Patkós, Zsolt Tuza, and Máté Vizer. *The robust chromatic number of graphs*. arXiv:2305.01923v1, 2023. Graphs and Combinatorics 40, article 89, 2024. [Preprint](https://arxiv.org/abs/2305.01923) and [journal record](https://doi.org/10.1007/s00373-024-02817-1).

[2] MathDB. *The strict lower-bound conjecture for the robust clique covering number*. Record 358270. [Record](https://mathdb.com/p/358270/the-strict-lower-bound-conjecture-for-the-robust-clique-cove).
