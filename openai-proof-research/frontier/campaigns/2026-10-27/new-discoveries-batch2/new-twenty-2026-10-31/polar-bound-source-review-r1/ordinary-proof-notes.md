# Independent ordinary proof — 357910

This is an ordinary mathematical review, not a Lean certificate. I independently reconstructed the graph and each deletion case. The small deterministic data comparison in check_and_inventory.py supplements this argument; it does not search partitions or prove nonpolarity computationally.

For a finite simple graph, complete multipartite means that reflexive nonadjacency is an equivalence relation: its classes are independent and every pair in different classes is adjacent. Equivalently, there is no induced K2+K1. Indeed failure of transitivity is precisely a vertex nonadjacent to the two adjacent endpoints of an edge. Conversely equivalence classes give the required partition. A cluster is a disjoint union of cliques, equivalently P3-free: every connected noncomplete graph has an induced P3 by a shortest path. The complement of a cluster with t components is complete t-partite, so the source's bound of at most k parts on the complemented B side is exactly at most k clique components in B. Infinity removes the bound on the number of A parts; it does not require infinitely many parts. Empty sides have zero parts; restriction discards empty parts and preserves both properties. Our displayed partitions have nonempty sides, so no empty-side convention affects this witness.

Let C=0123, S=4567 with edges 45,67, I=8,9,10,11. C is a clique complete to S; I is independent anticomplete to S. The only C-I edges are {2,3}×{8,9} and {0,1}×{10,11}. This is strict 2K2-split by definition, rather than pseudo-split or C4-split. All twelve vertices are present and distinct.

Suppose A is complete multipartite and B a cluster with at most four components. If all S were in A, vertices 4,5,6 would give K2+K1. Thus B meets S. If all four I vertices were in B, any vertex in B∩S together with I would be an independent five-set in B. Each independent vertex must belong to a different clique component, a contradiction. Hence some u∈I∩A exists. As u is anticomplete to S, neither edge of S can have both endpoints in A. Choose b in B∩{4,5} and d in B∩{6,7}; these exist and are nonadjacent. Any c∈C∩B would make b,c,d an induced P3. Consequently C⊆A. For u=8 or 9, the adjacent vertices 0,1 are both nonneighbors of u; for u=10 or 11 use 2,3. Either triple induces K2+K1 in A, a contradiction. These cases exhaust all polar partitions, including those with an empty side.

Deletion partitions, with explicit A parts (B components are separated by semicolons):

| deleted | A parts | B components |
|---|---|---|
|0|{1,8,9};{2};{3}|{4,5};{6,7};{10};{11}|
|1|{0,8,9};{2};{3}|{4,5};{6,7};{10};{11}|
|2|{3,10,11};{0};{1}|{4,5};{6,7};{8};{9}|
|3|{2,10,11};{0};{1}|{4,5};{6,7};{8};{9}|
|4|{5,8,9,10,11}|{0,1,2,3,6,7}|
|5|{4,8,9,10,11}|{0,1,2,3,6,7}|
|6|{7,8,9,10,11}|{0,1,2,3,4,5}|
|7|{6,8,9,10,11}|{0,1,2,3,4,5}|
|8|singletons of {0,1,2,3,4,5}|{6,7};{9};{10};{11}|
|9|singletons of {0,1,2,3,4,5}|{6,7};{8};{10};{11}|
|10|singletons of {0,1,2,3,4,5}|{6,7};{8};{9};{11}|
|11|singletons of {0,1,2,3,4,5}|{6,7};{8};{9};{10}|

For the first four rows the large A class is independent and complete to both other singleton classes, which are adjacent. In the next four rows A is independent and B is a clique. In the last four rows A is a clique and B consists of one edge and three isolated vertices. Thus every row is polar. Every proper induced subgraph omits a vertex and is an induced subgraph of that vertex deletion; restriction gives a polar partition. This proves hereditary minimality, not merely minimality among strict H-split graphs.

At k=4, c=i=4, the i interval 4≤4≤6 holds, but c≤2k-i-1 demands 4≤3. The twelve-vertex graph also exceeds 2k+3=11. This refutes the universal conjunction in the literal MathDB record. Neither the i clause alone, a general replacement bound, nor minimum counterexample order is proved.

The characterization in arXiv v1/v2 Lemma 39 is independently compatible: at i=k it requires at least two I vertices giving a complete multipartite C∪I′. In fact no single I vertex works, because it misses an adjacent C pair. After a C deletion, the appropriate two equal-neighborhood I vertices work; after an I deletion, i=3≤k-1; after an S deletion the graph is split and Lemma 39's strict hypothesis is no longer relevant. The lemma proof's extracted phrase 'I not subset A' cannot justify I∩A≠∅; the necessary assertion is I not subset B. The argument above supplies the correct implication and does not assume the misprinted/extracted phrase.
