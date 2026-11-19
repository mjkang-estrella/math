# A counterexample to the treewidth–connectivity partition conjecture

## Abstract

A finite simple graph on 16 vertices and 34 edges has treewidth 3 and vertex connectivity 3. For every independent vertex set, its induced complement either has treewidth at least 3 or admits a vertex deletion of size at most one that leaves a disconnected graph. This refutes MathDB 366258 and Conjecture 36 of Cambie, Dross, Knauer, La and Valicov in arXiv:2412.11774v2 at the integer parameter $k=3$. The concrete refutation has been reproduced from exact Lean source in two fresh layouts. The final section gives the ordinary extension to every integer $k\ge3$.

## 1. Statement and conventions

Conjecture 36 in the 29 October 2025 arXiv revision asks for the following partition. Given a graph $G$ with $\operatorname{tw}(G)\le k$ and vertex connectivity at least $k$, partition its vertices into an independent set $I$ and the vertex set of an induced graph $T$ with $\operatorname{tw}(T)\le k-1$ and vertex connectivity at least $k-1$. The retained MathDB statement specifies integer $k$. The native notation $G-S$ deletes the vertices of $S$ and all their incident edges, so in a partition $T=G[V(G)\setminus I]$. The conjecture uses undirected graph hypotheses. Its remarks give the cases $k=1$ and $k=2$, the latter referring to Theorem 10 on 2-vertex-connected simple series-parallel graphs, and separately describe a positive construction for $k$-trees. [Cambie–Dross–Knauer–La–Valicov, arXiv:2412.11774v2](https://arxiv.org/abs/2412.11774v2)

For positive $q$, we use the usual size-and-deletion convention for $q$-vertex-connectivity: $|V(G)|>q$ and $G-S$ is connected for every $S\subseteq V(G)$ with $|S|<q$. A tree decomposition consists of a nonempty tree of bags, each vertex occurring in at least one bag, each graph edge covered by a bag, and the bags containing each vertex inducing a connected subtree. Equivalently the unique path between any two bags containing a vertex consists entirely of bags containing it. An integer width bound $w$ means every bag has at most $w+1$ vertices. A finite graph's bags are automatically finite. Edge coverage already covers every non-isolated vertex. Under a convention allowing isolated vertices to be omitted, adding a singleton leaf bag for each missing vertex causes no width increase at the thresholds 2 and 3.

**Theorem.** There is a finite simple undirected graph $G$ with $|V(G)|=16$, $|E(G)|=34$, $\operatorname{tw}(G)=3$ and $\kappa(G)=3$ such that for every independent $I\subseteq V(G)$, $G-I$ has treewidth at least 3 or has a deletion of at most one vertex leaving at least two nonempty components.

## 2. Construction and connectivity

Use indices in $\mathbb Z/4\mathbb Z$. Start with a clique on $v_0,v_1,v_2,v_3$. For each $u$, introduce three private vertices $c_u,x_u,y_u$. Put every edge of the complete bipartite graph with sides
$$
L_u=\{c_u,v_{u+2},v_{u+3}\},\qquad
R_u=\{v_u,x_u,y_u\}.
$$
Take the union of these four bicliques and the core clique. The edge set consists of the six core edges and, for each $u$, exactly seven edges incident with a private vertex: $c_uv_u,c_ux_u,c_uy_u$ and the four edges from $v_{u+2},v_{u+3}$ to $x_u,y_u$. Thus there are $4+4\cdot3=16$ vertices and $6+4\cdot7=34$ distinct edges.

Let $S$ be any set of at most two vertices. The core minus $S$ is a nonempty clique. Both sides of each biclique still contain a vertex, so its surviving subgraph is connected, and among its three distinct core attachments $v_u,v_{u+2},v_{u+3}$ at least one remains. Thus every surviving private vertex can reach the surviving core. The whole surviving graph is connected. Conversely, deleting the three neighbors of any $c_u$ isolates $c_u$ while other vertices remain, so $\kappa(G)=3$.

## 3. Upper bound on treewidth

Let the bag tree have a root with bag $\{v_0,v_1,v_2,v_3\}$. For each $u$, attach to the root a node with bag
$$
B_{u,0}=\{v_{u+2},v_{u+3},c_u,v_u\}.
$$
Attach two children to that node with bags
$$
B_{u,1}=\{v_{u+2},v_{u+3},c_u,x_u\},\qquad
B_{u,2}=\{v_{u+2},v_{u+3},c_u,y_u\}.
$$
These thirteen nodes form a tree, with twelve parent-child edges. The root covers the core edges. The three bags for $u$ cover the biclique edges on $L_u,R_u$. Each $x_u$ or $y_u$ occurs only in its own leaf and $c_u$ occurs at exactly the three nodes of its branch. A core vertex occurs at the root, at the central node indexed by itself, and at all three nodes in each branch where it is one of the two offset core vertices. These occurrences are connected. All bags have four vertices, giving width at most three.

## 4. A lower bound valid for any bag tree

**Branch-set lemma.** Suppose a graph has a nonempty finite family of $m$ pairwise disjoint, nonempty connected vertex sets, with an edge between each pair of distinct sets. Every tree decomposition has a bag of size at least $m$, even if its bag tree has infinitely many nodes.

For a connected vertex set $B$, consider the nodes whose bags meet $B$. They form a nonempty connected subtree: the occurrence subtrees of consecutive vertices along a path in $B$ intersect at a bag covering their edge. A connecting path in $B$ therefore joins the occurrence subtree of any chosen vertex in one meeting bag to that of any chosen vertex in another. An edge between different branch sets makes their meeting subtrees intersect.

Here is the finite-family Helly argument for these subtrees. Root the bag tree at any node. Every nonempty connected subtree $S$ has a minimum-depth vertex $a_S$ because depths are nonnegative integers. This vertex is on the root path to every $z\in S$. Otherwise the common initial segment of the root paths to $a_S$ and $z$ ends at a strict ancestor of $a_S$ on the unique path from $a_S$ to $z$. That ancestor belongs to $S$ by path convexity, contradicting minimum depth. This also makes the minimum-depth vertex unique. Choose $S_*$ whose minimum-depth vertex has maximum depth among the finitely many subtrees. For any $S$, take $z\in S\cap S_*$. Both $a_S$ and $a_{S_*}$ are on the root path to $z$, and the depth inequality puts $a_{S_*}$ on the segment from $a_S$ to $z$. This segment belongs to $S$. Thus $a_{S_*}$ is in every meeting subtree. Its bag contains at least one vertex from each branch set, and disjointness makes those representatives distinct.

In a finite graph there is also no difference between existence of a finite and an unrestricted bag tree at these width thresholds. From any decomposition, select one node covering each vertex and one covering each edge. Include all unique paths from a chosen node to this finite selection. The result is a finite subtree, since each path has finite length. Restrict the bags to it. Coverage is preserved by construction, and any two retained occurrences remain joined by their unique original path inside the finite subtree. For an empty graph a single empty bag suffices at the thresholds used here.

Applying the lemma to the four singleton core vertices proves $\operatorname{tw}(G)\ge3$.

## 5. Every independent deletion fails

Let $I$ be an arbitrary independent set. If it misses the core, the four singleton core vertices are four touching branch sets in $G-I$, so $\operatorname{tw}(G-I)\ge3$. Otherwise independence in the clique gives exactly one core vertex $v_u\in I$. Its neighbors $v_{u+2},v_{u+3},c_u$ survive.

If either $x_u$ or $y_u$ belongs to $I$, the surviving $c_u$ has at most one neighbor in $G-I$. Delete the set of all its surviving neighbors. The center remains isolated and $v_{u+2}$ remains because it is a distinct nonneighbor of the center. The remainder is therefore disconnected and has at least two vertices regardless of conventions for degenerate graphs.

If both leaves survive, use the four branch sets
$$
\{v_{u+2}\},\quad \{v_{u+3}\},\quad \{x_u\},\quad \{c_u,y_u\}.
$$
The two core singletons touch by their clique edge. Each touches $x_u$ and touches $y_u$. The singleton $x_u$ touches $c_u$, and the last set is connected by $c_uy_u$. The sets are disjoint, so the branch-set lemma gives treewidth at least 3. All branches and cuts lie in the actual induced complement. These cases exhaust all independent sets, including the empty set.

Standard 2-vertex-connectivity requires a connected graph with at least three vertices and no cut vertex. In the missing-leaf case, an isolated center makes the complement disconnected. If the center has one neighbor and the complement is connected, deleting that neighbor separates the center from the surviving core, so the neighbor is a cut vertex. Every independent set meets at most one core vertex and at most two private vertices in each gadget, so the complement always has at least seven vertices.

## 6. Formal replay and provenance

The concrete theorem is the kernel-checked declaration `MathDB366258.native_refutation : ¬ MathDB366258.NativeConjecture`. The formal version quantifies over finite simple graphs and integer $k$ and uses the induced subtype on $I^c$ as the remainder. Connectivity tests every finite vertex deletion below the stated integer cardinality. On a finite graph, every vertex subset has a unique corresponding finite set with the same elements and cardinality, yielding precisely the standard vertex-deletion test. Lean's width proposition quantifies over an index type in a specified universe. Its lower-bound theorem is polymorphic in the node universe, and the concrete width witness uses a finite type of thirteen nodes. The argument in §4 gives the usual equivalence to finite index trees and to the running-intersection property.

A fresh byte-level extraction from the [exact Lean appendix](LEAN-SOURCE-APPENDIX.md) produced four split modules, each compiled and separately kernel-checked before any dependent module. The split build was then archived. The standalone module was compiled and separately kernel-checked in a new empty build directory at the pinned Lean 4.34.1 and Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`, against the pinned prebuilt upstream closure. All five source and five olean hashes match the author records. The axiom output matches all 10 split endpoint and 75 standalone entries, with roots drawn only from `propext`, `Classical.choice`, and `Quot.sound`. The [crosswalk](CROSSWALK.md) identifies the formal declarations and ordinary scope bridges. The [review report](REPORT.md) records the review boundaries, process deviations and source holds.

The contribution of this construction is the conjunction of the matching input width and connectivity and the forced dichotomy on every independent deletion. The native $k$-tree construction addresses a narrower positive class. The source's earlier figure examples concern CAI-partitions. In particular two opposite vertices of the cube are independent and their deletion leaves a six-cycle, which meets the proposed thresholds at $k=3$. The retained prior review identifies standard biclique neighbor forcing, width machinery, closures and isolation arguments as antecedent ingredients. Its comparison was bounded, and the EJC final, the selected Bodlaender delivery, and fresh registry qualification are held. These provenance limits leave priority and contribution qualification open.

## 7. Ordinary extension to every integer $k\ge3$

For such $k$, use a clique $C$ of size $k+1$. For each $u\in C$, choose any $A_u\subseteq C\setminus\{u\}$ of size $k-1$. Introduce a private center $c_u$ and a private leaf set $L_u'$ of size $k-1$. Add a complete bipartite graph with sides $A_u\cup\{c_u\}$ and $\{u\}\cup L_u'$, using no further edges beyond these bicliques and the core.

After fewer than $k$ deletions the surviving core is a nonempty clique. Each of the two $k$-vertex sides of every biclique and each $k$-vertex attachment set $A_u\cup\{u\}$ has a survivor. Therefore each surviving private vertex can reach the core. A width-$k$ decomposition uses root bag $C$, and for each $u$ a child bag $A_u\cup\{c_u,u\}$ carrying one leaf bag $A_u\cup\{c_u,x\}$ for every $x\in L_u'$. Its edge coverage and occurrence connectivity follow from the same descriptions as in §3. The core gives a width lower bound of $k$, and deleting the $k$ neighbors of a center shows connectivity exactly $k$.

If $I$ avoids $C$, the $k+1$ core singletons give the width obstruction. If $u\in I\cap C$, all of $A_u$ and $c_u$ survive. A missing private leaf then leaves at most $k-2$ surviving neighbors of $c_u$; removing those neighbors disconnects $c_u$ from every vertex of $A_u$. Otherwise choose two distinct leaves $x,y\in L_u'$, possible because $k\ge3$. The $k-1$ singleton vertices of $A_u$, the singleton $x$, and the pair $\{c_u,y\}$ give $k+1$ disjoint connected pairwise touching branch sets, proving width at least $k$ even in an unrestricted bag tree. This section is an ordinary argument. The replayed formal endpoint uses $k=3$.
