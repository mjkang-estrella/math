# Proof dossier: MathDB 355217

DRAFT; AI-assisted. Zero accepted credit. The finite graph result is formalized in the byte-identical packet; the structural results below are ordinary mathematical proofs.

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




## 6. Domain, source corrections and related work

The literal quantification in Conjecture 7.1 does not explicitly require connectivity. For an edgeless graph of order at least 2, M(G)=G. Under convention A the only dominating set is the whole vertex set, so the two minima equal n. Under convention B no dominating set leaves a nonempty complement, so there is no attained minimum. The formal numerical definition uses sInf of attainable natural cardinalities and returns 0 on this empty feasible set; that is a totalization, not a source minimum. This domain observation earns no credit and is not used in either connected refutation.

Uncredited correction to Theorem 4.12 of [1]. At K_(2,2)=C4 that theorem gives q(M(K_(2,2)))=2; the correct value is 3, consistent with [1, Theorem 4.10]. By the equality characterization, a two-node set would have to be a perfect matching, but deleting either matching from C4 leaves two disjoint edges. For an explicit upper witness, label C4 cyclically 1,2,3,4 and take {m_12,3,4}. The remaining nodes form the path 2–m_23–m_34–m_41–1, so the complement is connected; the set dominates. Thus the minimum is exactly 3. The strict inequality still holds here, since q(C4)=2.

Uncredited correction to Section 7 of [1]. For the friendship graph F_k with k ≥ 2 triangular blades, the claimed original-graph value 1 is incorrect: q(F_k)=k. If the hub is not selected, domination forces at least one vertex from every blade pair. Selecting exactly one per pair gives a connected complement consisting of the hub and its surviving neighbors. If the hub is selected, connectivity confines the complement to one pair, so at least 2k−1 vertices must be selected, which is at least k. The middle value k+1 stated in [1, Theorem 4.13] leaves a gap of only 1. Neither correction is part of the formal packet or a claim for credit.

Related work and limits. The source attributes outer-connected domination to Cyman [4] and the middle-graph construction to Hamada and Yoshimura [5]. Those historical attributions and bibliographic data are taken from [1]; their full texts were not accessed here. The later paper [2] studies total outer-connected domination, a different parameter, and cites [1] as a preprint. Its cached text contains no discussion of Conjecture 7.1.

The mathematical review's dated arXiv/OpenAlex check (3 November 2026 UTC) reported v1 only, no journal reference and zero recorded OpenAlex citations, including a zero-result citing-works query. It read the top 100 titles from each of two broad topic searches; this is bounded coverage. There was no Scholar, MathSciNet, zbMATH or publisher clearance. This lane used only cached evidence and no network, and makes no fresh claim about live publication or citation status.

Root's registry-refresh receipt (4 November 2026 UTC) records OpenAI head 4eaee87548250b2682affda7d05d947c05554bae and Omega head 854c40015525e1797989db6692fb77069d3c0879, with no keyword hits in complete Omega D5 and Problems path trees. A path screen is not a full-body proof search. No worldwide priority is asserted. The arXiv-only, apparently uncited source and the short step from friendship graphs make the external significance modest.


## 7. Formal correspondence, audits and trust limits

The source-only packet uses Lean 4.34.1 and mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. All names below lie in namespace R139.MiddleOCD. The formal middle graph has the literal type Fin 8 ⊕ G8.edgeSet; no unproved isomorphism to a labeled 19-node graph is used.

See paper.pdf, Section 7, and evidence/middle-formal-r1/STATEMENT-CORRESPONDENCE.md for the correspondence table.

The four value endpoints assert IsLeast on attainable cardinalities, so they supply actual witnesses and lower bounds independently of any empty-set sInf default. The final universal negations are separate for A and B and quantify over finite types and connected simple graphs of order at least 2. Each specializes to Fin 8 and reduces the proposed inequality to 4 < 4.

The formal lower bound for G8 uses 93 individual certificates, one for each subset of size at most 3, followed by a proved coverage lemma. Each certificate gives an undominated vertex or a closed component separating complement vertices. The middle lower bound is generic vertex-node counting. Parent maps with strictly decreasing depths certify connectivity for the upper witnesses and G8 itself. Offline generation supplies no trusted proof oracle.

The formal handoff and fidelity review report a declaration-closure audit of 252,066 declarations with inventory equal to audited set, 207 local declarations and no missing dependency names. Local metadata and transitive axioms pass the restrictions; endpoint axiom lists are exactly propext, Classical.choice and Quot.sound. Upstream compiler/runtime metadata is reported separately, including unsafe and partial machinery; the audit does not claim all upstream declarations lack it. The review also scans source with comments and strings removed. Kernel checking, not a lexical scan, supplies proof assurance.

Three negative controls reject the value 3, original-vertex adjacency in the middle graph, and a disconnected complement witness. They fail by false-proposition diagnostics rather than timeout or import error. Independent Python checks recover both minima and both conventions. The fidelity review reports A–D PASS and E QUALIFIED_PASS with eight manuscript conditions; their disposition is recorded in gate-E.md.

Root's separate replay-result.json (4 November 2026 UTC) reports safe fresh extraction, five serial strict module builds and explicit-module leanchecker passes, all three negative controls rejected, regression PASS, and allowed endpoint axioms. It reads pinned upstream oleans rather than rebuilding all dependencies from source. This manuscript lane did not run Lean. Recorded replay calls used two CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB, MALLOC_ARENA_MAX=2 and one heavy process at a time. Audit tooling, compiler/kernel, pinned library artifacts and the operating environment remain trust dependencies. The family, characterization, classification and literature assessment are outside the finite Lean theorem.


