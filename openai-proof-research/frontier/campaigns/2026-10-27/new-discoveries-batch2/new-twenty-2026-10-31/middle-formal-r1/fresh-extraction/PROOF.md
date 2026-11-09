G8 has vertices 0 through 7 and edges 01, 06, 16, 23, 27, 37, 46, 47, 56, 57, 67.

The set S0 = {0, 2, 4, 5} dominates G8. Its complement is connected by the path 1–6–7–3. Every set of at most 3 vertices fails: the formal certificate enumerates exactly the 93 such sets, and for each supplies either an undominated vertex or an explicit closed component and an outside vertex. These are individual kernel proofs, followed by a separately checked coverage lemma. No computed graph search result is assumed.

For a human proof, split on membership of hubs 6 and 7. If neither belongs to S, domination forces 4 and 5 and one member of each of {0,1}, {2,3}. If just hub 6 belongs, connectivity forces both 0 and 1 into S (otherwise their surviving component cannot reach 7); domination forces a member of {2,3}. The other case is symmetric. If both hubs belong, a connected complement lies inside one of {0,1}, {2,3}, {4}, {5}, forcing at least 6 elements in S.

In the middle graph, a chosen original vertex covers one original vertex, and a chosen edge covers at most two. The generic formal lemma partitions original vertices by a chosen dominator and bounds each fiber by two. Thus 8 ≤ 2 |D| and |D| ≥ 4.

The four edge nodes 01, 23, 46, 57 dominate the middle graph. After removing them, the seven other edges form the tree 06, 16, 56, 67, 27, 37, 47. A parent map and a strictly decreasing natural depth certify connectivity directly on the literal type Fin 8 ⊕ G8.edgeSet.

Both witnesses leave nonempty complements. The lower bounds work even with vacuous preconnectivity, so both conventions have exact minimum 4. Applying either proposed strict inequality to the proved connected graph G8 yields 4 < 4.

Only this finite connected counterexample is formalized. The infinite family, uniqueness search, and prior-art claims from the discovery and review lanes are not new formal endpoints here. Root decides significance and acceptance. Credit remains zero.

Source-error remarks (inherited review, uncredited): Theorem 4.12 gives the wrong value at K_{2,2}; the correct middle value is 3. Section 7 states the friendship graph's outer-connected domination number as 1, whereas it is n for F_n. These remarks are not used by the formal proof.
