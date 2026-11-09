# MathDB 322229: no full proof obtained

Source: Hu–Xu, *Roman Bondage Number of a Graph*, arXiv:1109.3930v1, Conjecture 5.1. The literal target is every finite simple connected graph of order at least three. Roman domination uses vertex labels 0,1,2 and requires every zero to have an adjacent 2. Its weight is the sum of labels; gamma_R is its minimum. The Roman bondage number is the minimum size of an edge deletion strictly increasing gamma_R. The requested bound is b_R <= 2 Delta + kappa - 3. Source Theorem 5.6 proves the corresponding lambda bound. Whitney's inequality goes in the wrong direction for replacing lambda with kappa.

## Sustained route and exact reductions

1. **Local path deletion.** Source Theorems 5.1 and 5.2 bound b_R using a three-vertex path x,y,z by the smaller of
   d(x)+d(y)+d(z)-|N(y) intersect (N(x) union N(z))|-3,
   d(x)+d(y)+d(z)-|N(y) intersect (N(x) union N(z))|-|N(x) intersect N(z)|-1.
   This proves many cases, including the minimum-degree bound, but is insufficient in general. Here is a precise obstruction to that shortcut, not a counterexample to the conjecture: take two disjoint copies of K_{4,4}; in each remove one edge ab and replace it by the two edges av,bv, using the same new vertex v for both copies. This is a connected triangle-free 4-regular graph on 17 vertices with cut vertex v, so kappa=1 and the conjectured bound is 6. Every local first bound is 9. In the second bound the middle-neighborhood correction is zero (triangle-free) and common-neighborhood size is at most 4, so it is at least 7. Thus neither source path estimate can reach 6 on this graph. A new argument is required.

2. **Vertex-isolation/criticality reduction.** If some vertex u satisfies gamma_R(G-u)>=gamma_R(G), deleting all incident edges produces an isolated vertex and increases gamma_R by at least one. Consequently b_R(G)<=d(u)<=Delta. For any graph, gamma_R(G-u)>=gamma_R(G)-1, since a minimum RDF on G-u extends by assigning u=1. Thus any graph with b_R>Delta must satisfy gamma_R(G-u)=gamma_R(G)-1 for every u. Since 2 Delta+kappa-3>=Delta for connected order>=3, any counterexample must have this vertex-critical property. This is a routine source-compatible reduction, not a discovery.

3. **Attempted separator shortcut falsified.** Vertex-criticality does not imply absence of cut vertices. An exact six-vertex example has edges 03,04,05,12,13,14,23,24. It has gamma_R=4; deleting any vertex gives gamma_R=3; vertex 0 is a cut vertex; Delta=3; b_R=3. This defeats the proposed elimination of the kappa=1 case by criticality alone. It satisfies the conjecture (target 4). This example was found by exhaustive integer enumeration, and is not presented as a new mathematical result. The later primary article *Critical graphs with Roman domination number four*, DOI 10.1016/j.akcej.2019.12.015, also explicitly reports critical graphs with cut vertices in its publicly indexed body. Direct publisher retrieval returned 403; that article is not used as a proof dependency.

4. **Beyond failed shortcuts.** Isolating a minimum separator S costs up to |S| Delta edges, which exceeds the permitted 2 Delta+|S|-3 once the separator is large; blindly replacing an edge cut by a vertex cut does not preserve the budget. The next concrete mechanism is a separator-state lemma that tracks each vertex's label (0/1/2) and whether each zero is already dominated inside a component. A successful argument must produce an increasing deletion set inside the stated budget, not merely a decomposition of gamma_R. No such lemma was proved here. Cases lambda=kappa already follow from source Theorem 5.6 and are ineligible routine corollaries. The remaining genuinely difficult region has kappa<lambda<=delta and vertex-criticality, with the local path bounds also potentially too large.

## Finite diagnostic and adversarial checks

`roman_diagnostic.py` enumerates all labelled simple graphs at each order 3–6. It computes gamma_R exactly as

    min over S subset V [2 |S| + |V minus N[S]|].

For fixed 2-labelled set S, every undominated vertex must be labelled 1 and all other vertices can be labelled 0, proving this finite minimization formula. It computes bondage recursively over all proper one-edge deletions: if gamma increases, distance is 1; otherwise it is 1 plus that deletion's bondage distance. Increasing gamma is monotone under deletion, so a shortest path to an increase has this recurrence. Graphs having gamma_R=|V| have no increasing deletion and receive an internal sentinel; none is connected at order>=3. Connectivity is computed by bitset reachability; all separator subsets are tested. There are 27,474 connected labelled graphs (4,38,728,26,704). No violations were found. Labels produce repeated isomorphism classes; these are not 27,474 distinct graph types. All arithmetic is integer, but this code is not Lean and the result is not a universal theorem or accepted certificate.

The 17-vertex local-bound obstruction above is purely structural and does not rely on the sweep. The finite absence of counterexamples establishes neither the conjecture nor novelty. The strong claim that criticality forces connectivity two was explicitly tested and rejected rather than used as a bridge.

## Formal endpoint and dependencies

No strong full ordinary proof survived, so there is no implemented Lean endpoint to recommend for independent acceptance review. A future exact endpoint would quantify over `(n : Nat)` and `(G : SimpleGraph (Fin n))`, assume `3 <= n` and `G.Connected`, and conclude the integer inequality for fully defined `romanBondage G`, `maxDegree G` and `vertexConnectivity G`. It must include the equivalence of the RDF definition and finite minimization, exact edge-deletion operation, actual minima, and the standard complete-graph connectivity convention. The endpoint cannot assume the separator lemma, optimality, a graph-bound bridge or any unproved equality.

No Lean/mathlib pin, transitive axiom audit or extracted replay exists for this target. Therefore zero credit is proposed. A finite-graph combinatorial proof would have reasonable formalization prospects; a finite sweep alone cannot provide the all-order endpoint. Independent fidelity review would still be required even after a kernel proof.
