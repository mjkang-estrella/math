# Statement correspondence and limitations

Source: Bača, Semaničová-Feňovčíková, Lai and Wang, Fundamenta Informaticae 185(2) (2022), 99–113, arXiv:2204.04479v2. Published Conjecture 6.1 is MathDB 354228. HTML numbering differs: its Lemmas 2.13 and 2.15 are published Lemmas 2.9 and 2.10.

| Fidelity item | Implementation | Status |
| --- | --- | --- |
| (i) Source Definitions 1.1–1.3 | AntimagicBasics: Labeling, weight, IsLocal, spectrum, chiLA | Defined literally; minimum theorem from IsLeast proved. General existence for all graphs is not proved. |
| Source standing exclusions | NoK2Component; Definition 1.1 also excludes isolated vertices | Definitions extend harmlessly to all finite graphs. No generic existence is claimed even under the exclusions. |
| (ii) Concrete T(t,n) | Vertex, Child, tree, root | Genuine Fintype and decidable instances; tree structure remains ModelStructure. |
| Structural source definition | FullTree requires G.IsTree, depth, unique parent, adjacency, full child count, common terminal depth n | Child count is t below n and zero at n. For t >= 2 this is equivalent to the source's nonleaf/leaf convention. Equivalence to a path-distance formulation is not yet separately proved. |
| (iii) Least t^n + 1 | even_case | Conditional on LowerBound and Construction. |
| Explicit labelling | label, internalLabel, largeLabel, depthTwoLabel | Total piecewise formula; Construction states exact agreement on graph edges, plus properness and colour count. |
| (iv) Arbitrary-tree bridge | ModelBridge | Unproved Prop; no isomorphism is presumed in the input FullTree. |
| (iv) Invariance | AntimagicIso | Proved unconditionally for arbitrary finite simple graphs. |
| Number of leaves | numLeaves counts degree-one vertices | Canonical count remains ModelLeaves. |
| Full MathDB statement | mathdb_354228 | Conditional IsLeast and chiLA equality for arbitrary FullTree G t n. |

All theorem quantifiers require t >= 2, Even t and n >= 1 as appropriate. Depth zero is outside the source's nontrivial scope. A generic FullTree has an actual root/depth/child structure and a graph-theoretic tree proof, not an assumed isomorphism to the canonical graph.

The depth-two binary labels are credited to published Figure 5. The t >= 4 depth-two construction is assembled from published source ingredients, including Lemmas 2.2 and 2.9. The reviewed parity-shell construction for n >= 3 is the proposed new mathematical contribution; this round does not certify that contribution in full scope.
