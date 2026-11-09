# A connected eight-vertex counterexample to strict increase of outer-connected domination under the middle-graph operation

DRAFT for root review • MathDB 355217 • 4 November 2026 (UTC)

Prepared with AI assistance by the Codex manuscript lane. No human authorship or affiliation is asserted. This draft carries zero accepted credit; root reads the paper and decides acceptance.

## Abstract

We give a connected simple graph G8 of order 8 for which the outer-connected domination numbers of G8 and its middle graph are both 4. This refutes the connected restriction of Conjecture 7.1 of Kazemnejad, Pahlavsay, Palezzato and Torielli [1]. Both minima are attained under either convention for connectivity of the empty complement. We give short proofs, an infinite equality family, and a characterization of equality in the middle-graph counting bound by a perfect matching whose deletion leaves a connected spanning graph. Only the finite counterexample is certified by the supplied Lean packet. Smallest-order uniqueness is reported as exhaustive computation. The significance is modest, and no priority claim is made.

## 1. Definitions and the source question

All graphs here are finite, undirected and simple. Write q(G) for the source's outer-connected domination number, denoted γ̃c(G). A set S dominates G when N_G[v] ∩ S ≠ ∅ for every vertex v. Thus a vertex in S dominates itself.

Definition 1.2 of [1] reads: “A dominating set S of a graph G is called an outer-connected dominating set if the graph G − S is connected. The minimum cardinality of an outer-connected dominating set of G is called the outer-connected domination number of G and it is denoted by γ̃c(G).”

Definition 1.3 of [1] reads: “The middle graph M(G) of a graph G is the graph whose vertex set is V(G) ∪ E(G), where two vertices x, y in the vertex set of M(G) are adjacent in M(G) if one the following holds (1) x, y ∈ E(G) and x, y are adjacent in G; (2) x ∈ V(G), y ∈ E(G), and x, y are incident in G.”

We implement the union as a tagged disjoint union. Write m_uv for the node representing edge uv. Original vertex nodes are pairwise nonadjacent; edge nodes are adjacent exactly when distinct and sharing an endpoint. Incidence adjacency is undirected.

Conjecture 7.1 of [1], verbatim with mathematical typography normalized, is: “Let G be a graph of order n ≥ 2. Then γ̃c(G) < γ̃c(M(G)).” It is on page 11 and is reproduced in MathDB 355217 [3].

The source motivates this with trees (Corollary 4.5), complete graphs, cycles, wheels, complete bipartite graphs and friendship graphs (Theorems 4.8 and 4.10–4.13). Its evidence includes errors discussed in Section 6. The counterexample below is connected and has edges, independently of any ambiguity in “non-empty” in the source's standing assumptions.

===PAGE===
## 2. A connected counterexample and its original-graph minimum

Theorem 1. Let V(G8) = {0,1,2,3,4,5,6,7} and let its complete edge list be

01, 06, 16, 23, 27, 37, 46, 47, 56, 57, 67.

Then G8 is connected and q(G8) = q(M(G8)) = 4, under each empty-complement convention. In particular the assertion “for every connected simple graph G of order at least 2, q(G) < q(M(G))” is false under each convention separately.

Connectivity of G8 follows already from the spanning tree with edges 06, 16, 56, 67, 27, 37, 47. The graph consists of triangles {0,1,6} and {2,3,7}, the hub edge 67, and two vertices 4 and 5 each joined to both hubs.

Convention A permits an empty complement (vacuous preconnectivity); convention B requires a nonempty connected complement. One-vertex complements are connected in both. The source does not specify the empty-complement convention. We use the appropriate minimum in each assertion; existence will be witnessed, rather than supplied by a totalized numerical definition.

Proof of q(G8) ≤ 4. Take S0 = {0,2,4,5}. The omitted vertices 1 and 3 are adjacent to 0 and 2, respectively, and both hubs are adjacent to 4. The complement contains the path 1–6–7–3, including all its vertices. Thus S0 dominates and leaves a nonempty connected complement.

Proof of q(G8) ≥ 4. Suppose S is outer-connected dominating with |S| ≤ 3. Its complement R has at least 5 vertices. Split according to membership of hubs 6 and 7.

Case 1: neither hub is in S. Domination of 4 and 5 forces 4,5 ∈ S. Domination of 0 forces S to meet {0,1}, since N[0] = {0,1,6}. Likewise S meets {2,3}. These four disjoint requirements give |S| ≥ 4.

Case 2: 6 ∈ S and 7 ∉ S. The surviving hub 7 is in R. If a vertex of {0,1} survived, its entire component in G8[R] would lie in {0,1}, since its only possible neighbor outside that pair is 6. It could not reach 7. Hence both 0 and 1 belong to S. Domination of 2 now requires a member of {2,3}, because N[2] = {2,3,7}. Together with 6 this again requires four vertices.

Case 3: 7 ∈ S and 6 ∉ S. Interchange the two triangles and the two hubs in Case 2. Both 2 and 3 must belong to S, as must a member of {0,1}; counting 7 gives |S| ≥ 4.

Case 4: both hubs are in S. Removing them leaves components {0,1}, {2,3}, {4}, {5}. A nonempty connected R must lie inside one such component, so |R| ≤ 2 and |S| ≥ 6, a contradiction.

All four cases exclude |S| ≤ 3. The same proof applies under both conventions, since R is nonempty throughout. This proves the first exact attained minimum.

===PAGE===
## 3. The middle-graph minimum and a structural characterization

Counting bound. For any graph G of order n, every dominating set D of M(G) satisfies n ≤ 2|D|. Indeed, the n original vertex nodes must be covered by closed neighborhoods of nodes in D. An original node covers just itself among these n nodes; an edge node covers its two endpoints. The union therefore has size at most 2|D|. This proves q(M(G8)) ≥ 4 and is the elementary mechanism behind [1, Theorem 4.1]. Connectivity is not needed for this bound.

Proof of q(M(G8)) ≤ 4. Take the edge-node set D8 = {m_01,m_23,m_46,m_57}. Its edges form a perfect matching F. Every original vertex is incident with its matching edge. Every other edge shares an endpoint with a matching edge, so every edge node is dominated as well.

After deleting D8, all original vertices and the edge nodes corresponding to the spanning tree 06, 16, 56, 67, 27, 37, 47 remain. Incidence edges subdivide that tree, forming a connected spanning subgraph of M(G8) − D8. Thus the complement is nonempty and connected. The two bounds prove its exact attained minimum 4 and complete Theorem 1. The graph M(G8) has 19 nodes and 48 edges.

Theorem 2 (ordinary mathematical result; not a packet endpoint). Let G be a connected finite simple graph of even order n ≥ 2. Under either convention,

q(M(G)) = n/2 if and only if G has a perfect matching F such that the spanning graph G − F is connected.

Proof, reverse direction. Suppose such F exists and select its n/2 edge nodes as D. Exactly as above, D dominates every original and edge node. The incidence subdivision of G − F is connected and spans the remaining middle graph, proving outer-connectivity. The counting bound gives equality.

Proof, forward direction. Since G is connected and n ≥ 2, M(G) is connected and has more than one vertex. Taking all but one of its vertices supplies a feasible set under both conventions, so its minimum is attained. Let D attain n/2, and let r of its nodes be original nodes. Its coverage of original vertices is at most r + 2(|D| − r) = n − r. Hence r = 0. The n/2 selected edge nodes must have disjoint endpoint pairs, since otherwise their union would cover fewer than n original vertices. Their edges therefore form a perfect matching F.

The complement contains every original node and precisely the nodes for edges of G − F. It has the same connected components as G − F: every incidence step remains within a component of G − F, and an adjacency between two remaining edge nodes also stays within one component because their edges share an endpoint. Thus any path between original nodes in the complement projects, by inserting shared endpoints at edge–edge steps, to a walk in G − F. Connectivity of the complement forces G − F connected. This also covers n = 2: its only connected graph has no such matching with connected remainder and does not attain n/2. □

This characterization is a direct refinement of the counting and matching constructions already visible in [1]. It is not presented as a deep independent mechanism.

===PAGE===
## 4. An infinite family of equality cases

Theorem 3 (ordinary mathematical result; not a packet endpoint). For integers a,b ≥ 1, define G_(a,b) with hubs x,y, twins t,u, pairs {α_i,β_i} for 1 ≤ i ≤ a and {γ_j,δ_j} for 1 ≤ j ≤ b. All these vertices are distinct. Its edges are exactly

xy, xt, yt, xu, yu; xα_i, xβ_i, α_iβ_i; yγ_j, yδ_j, γ_jδ_j.

Then n = 2a + 2b + 4 and q(G_(a,b)) = a + b + 2 = q(M(G_(a,b))) under both conventions. The member G_(1,1) is G8 under x=6, y=7, t=4, u=5, (α_1,β_1)=(0,1), (γ_1,δ_1)=(2,3).

Proof of the upper bound for G. Choose

S = {t,u} ∪ {α_i : 1 ≤ i ≤ a} ∪ {γ_j : 1 ≤ j ≤ b}.

The surviving hubs x,y are adjacent; each surviving β_i is adjacent to x and each δ_j to y. This complement is nonempty and connected. The chosen α_i dominate β_i, and γ_j dominate δ_j. Vertices t,u dominate both hubs. Thus S is outer-connected dominating and has a+b+2 elements.

Proof of the lower bound for G. It suffices to exclude smaller sets S. Their complements are nonempty, and the following hub cases apply.

Neither hub in S: domination forces t,u ∈ S and at least one vertex from every triangle pair. Hence |S| ≥ 2+a+b.

Only x in S: since y survives, no vertex in any x-triangle pair can survive; otherwise its component could not reach y. All 2a pair vertices at x must belong to S. Each of the b pairs at y must meet S by domination. Thus |S| ≥ 1+2a+b ≥ a+b+2, using a ≥ 1.

Only y in S: the symmetric argument gives |S| ≥ 1+a+2b ≥ a+b+2, using b ≥ 1.

Both hubs in S: the complement lies in a single triangle pair or a singleton twin, so it has at most two vertices. Hence |S| ≥ n−2 = 2a+2b+2 ≥ a+b+2. This completes all four cases.

Proof for the middle graph. The edges

F = {xt,yu} ∪ {α_iβ_i : 1 ≤ i ≤ a} ∪ {γ_jδ_j : 1 ≤ j ≤ b}

form a perfect matching. After deleting them, xy, yt and xu remain, and every triangle vertex remains adjacent to its hub. Consequently G − F is connected. Theorem 2 gives q(M(G)) = n/2 = a+b+2, as required. All upper witnesses have nonempty complements, so the argument is independent of the empty-complement convention. □

The hypotheses a,b ≥ 1 matter: if a=0, the “only x” case no longer supplies the asserted bound. Structurally, these graphs attach friendship blades to the two degree-three vertices of a diamond. G8 is a small design step from the friendship examples in the source, which limits the significance of the construction.

===PAGE===
## 5. Exhaustive computation and reproducibility

The following is a computational observation up to isomorphism, not a Lean theorem: among connected graphs of orders 2 through 8, there is no failure of the strict inequality below order 8, and exactly one failure at order 8, represented by G8. It is equality, not a strict reversal. Nothing here classifies larger counterexamples.

The discovery computation and the independent mathematical review used separate generators and searches. The review generator adds a vertex with every possible neighborhood to each smaller representative, then removes duplicates by refinement buckets and an exact backtracking isomorphism test. Every isomorphism class has a representative because deleting a vertex gives a smaller class already represented; neighborhood augmentation restores the graph. Counts by order 1,2,3,4,5,6,7,8 were:

All graphs: 1, 2, 4, 11, 34, 156, 1044, 12346.

Connected graphs: 1, 1, 2, 6, 21, 112, 853, 11117.

These agree with the familiar unlabeled graph counts reported in the review. The connected search range is orders 2–8 (the order-1 count is a generator check). The review computes q(G) by enumerating all subsets and decides whether M(G) has a feasible set of size at most q(G) by exact branching on an undominated node with smallest closed neighborhood. At a dominating partial set, all supersets of the target size must still be tested: outer-connectivity is not monotone under adding vertices. Thus dominating partial sets cannot simply terminate the search.

Cross-validation against plain middle-graph subset enumeration covered 189 graphs of orders 2–6 with middle order at most 16, under both conventions: 378 comparisons, zero mismatches. The unique order-8 output in the review labeling has edges 04, 06, 15, 17, 26, 27, 36, 37, 46, 57, 67; the review checks its isomorphism to G8. A separate literal subset enumeration finds 8 minimum sets in G8 and 2 in M(G8), under each convention. The two latter sets are {m_01,m_23,m_46,m_57} and {m_01,m_23,m_47,m_56}.

The dossier includes review scripts gen.py, search.py, mocd.py and crosscheck.py, class data all1.txt through all8.txt, and the original logs, as well as the discovery scripts and formal regression. The manuscript lane independently rechecks the fixed witness but does not rerun the full classification. Computation supplements rather than proves Theorem 1; the human proof and the finite Lean certificate do not depend on generator completeness.

Reproducibility boundaries. REPRODUCE.md describes the artifact layout, integrity checks, safe archive extraction and the historical pinned Lean replay procedure. The source-only ZIP is reused byte for byte, with SHA-256

5a3e8ac8153651c55942d8f1288b50dd0c578b089c02d01c353b750b2c5bb62b.

This lane performs safe extraction and byte comparison without invoking Lean, lake or leanchecker. The supplied independent review and root replay receipts describe runs in their own lanes. A new Lean replay is not claimed here. Hash manifests bind copied evidence and all frozen inputs before and after this work.

===PAGE===
## 6. Domain, source corrections and related work

The literal quantification in Conjecture 7.1 does not explicitly require connectivity. For an edgeless graph of order at least 2, M(G)=G. Under convention A the only dominating set is the whole vertex set, so the two minima equal n. Under convention B no dominating set leaves a nonempty complement, so there is no attained minimum. The formal numerical definition uses sInf of attainable natural cardinalities and returns 0 on this empty feasible set; that is a totalization, not a source minimum. This domain observation earns no credit and is not used in either connected refutation.

Uncredited correction to Theorem 4.12 of [1]. At K_(2,2)=C4 that theorem gives q(M(K_(2,2)))=2; the correct value is 3, consistent with [1, Theorem 4.10]. By the equality characterization, a two-node set would have to be a perfect matching, but deleting either matching from C4 leaves two disjoint edges. For an explicit upper witness, label C4 cyclically 1,2,3,4 and take {m_12,3,4}. The remaining nodes form the path 2–m_23–m_34–m_41–1, so the complement is connected; the set dominates. Thus the minimum is exactly 3. The strict inequality still holds here, since q(C4)=2.

Uncredited correction to Section 7 of [1]. For the friendship graph F_k with k ≥ 2 triangular blades, the claimed original-graph value 1 is incorrect: q(F_k)=k. If the hub is not selected, domination forces at least one vertex from every blade pair. Selecting exactly one per pair gives a connected complement consisting of the hub and its surviving neighbors. If the hub is selected, connectivity confines the complement to one pair, so at least 2k−1 vertices must be selected, which is at least k. The middle value k+1 stated in [1, Theorem 4.13] leaves a gap of only 1. Neither correction is part of the formal packet or a claim for credit.

Related work and limits. The source attributes outer-connected domination to Cyman [4] and the middle-graph construction to Hamada and Yoshimura [5]. Those historical attributions and bibliographic data are taken from [1]; their full texts were not accessed here. The later paper [2] studies total outer-connected domination, a different parameter, and cites [1] as a preprint. Its cached text contains no discussion of Conjecture 7.1.

The mathematical review's dated arXiv/OpenAlex check (3 November 2026 UTC) reported v1 only, no journal reference and zero recorded OpenAlex citations, including a zero-result citing-works query. It read the top 100 titles from each of two broad topic searches; this is bounded coverage. There was no Scholar, MathSciNet, zbMATH or publisher clearance. This lane used only cached evidence and no network, and makes no fresh claim about live publication or citation status.

Root's registry-refresh receipt (4 November 2026 UTC) records OpenAI head 4eaee87548250b2682affda7d05d947c05554bae and Omega head 854c40015525e1797989db6692fb77069d3c0879, with no keyword hits in complete Omega D5 and Problems path trees. A path screen is not a full-body proof search. No worldwide priority is asserted. The arXiv-only, apparently uncited source and the short step from friendship graphs make the external significance modest.

===PAGE===
## 7. Formal correspondence, audits and trust limits

The source-only packet uses Lean 4.34.1 and mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. All names below lie in namespace R139.MiddleOCD. The formal middle graph has the literal type Fin 8 ⊕ G8.edgeSet; no unproved isomorphism to a labeled 19-node graph is used.

FORMAL_TABLE

The four value endpoints assert IsLeast on attainable cardinalities, so they supply actual witnesses and lower bounds independently of any empty-set sInf default. The final universal negations are separate for A and B and quantify over finite types and connected simple graphs of order at least 2. Each specializes to Fin 8 and reduces the proposed inequality to 4 < 4.

The formal lower bound for G8 uses 93 individual certificates, one for each subset of size at most 3, followed by a proved coverage lemma. Each certificate gives an undominated vertex or a closed component separating complement vertices. The middle lower bound is generic vertex-node counting. Parent maps with strictly decreasing depths certify connectivity for the upper witnesses and G8 itself. Offline generation supplies no trusted proof oracle.

The formal handoff and fidelity review report a declaration-closure audit of 252,066 declarations with inventory equal to audited set, 207 local declarations and no missing dependency names. Local metadata and transitive axioms pass the restrictions; endpoint axiom lists are exactly propext, Classical.choice and Quot.sound. Upstream compiler/runtime metadata is reported separately, including unsafe and partial machinery; the audit does not claim all upstream declarations lack it. The review also scans source with comments and strings removed. Kernel checking, not a lexical scan, supplies proof assurance.

Three negative controls reject the value 3, original-vertex adjacency in the middle graph, and a disconnected complement witness. They fail by false-proposition diagnostics rather than timeout or import error. Independent Python checks recover both minima and both conventions. The fidelity review reports A–D PASS and E QUALIFIED_PASS with eight manuscript conditions; their disposition is recorded in gate-E.md.

Root's separate replay-result.json (4 November 2026 UTC) reports safe fresh extraction, five serial strict module builds and explicit-module leanchecker passes, all three negative controls rejected, regression PASS, and allowed endpoint axioms. It reads pinned upstream oleans rather than rebuilding all dependencies from source. This manuscript lane did not run Lean. Recorded replay calls used two CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB, MALLOC_ARENA_MAX=2 and one heavy process at a time. Audit tooling, compiler/kernel, pinned library artifacts and the operating environment remain trust dependencies. The family, characterization, classification and literature assessment are outside the finite Lean theorem.

## References

[1] F. Kazemnejad, B. Pahlavsay, E. Palezzato and M. Torielli. Connected and outer-connected domination number of middle graphs. arXiv:2206.15439v1, 2022. https://arxiv.org/abs/2206.15439v1.

[2] Same authors. Total outer-connected domination number of middle graphs. arXiv:2308.02127v1, 2023. https://arxiv.org/abs/2308.02127v1.

[3] MathDB 355217. Strict middle-graph increase conjecture for outer-connected domination. Cached corpus record; retrieval source probxiv_2026-09-29. https://mathdb.com/p/355217/strict-middle-graph-increase-conjecture-for-outer-connected.

[4] J. Cyman. The outer-connected domination number of a graph. Australasian Journal of Combinatorics 38 (2007), 35–46. Bibliographic data as in [1]; not independently accessed.

[5] T. Hamada and I. Yoshimura. Traversability and connectivity of the middle graph of a graph. Discrete Mathematics 14 (1976), 247–255. Bibliographic data as in [1]; not independently accessed. No unverified DOI is supplied.
