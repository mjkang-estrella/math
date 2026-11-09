# 357910: ordinary counterexample, awaiting source and significance review

Zero credit. No Lean execution was undertaken. Root should have the finite endpoint independently reviewed before assigning Pi implementation. A complete ordinary proof follows; journal figure comparison and bounded prior-art clearance remain qualified as described below.

## Exact object

Set k = 4. Vertices are C = {0,1,2,3}, S = {4,5,6,7}, I = {8,9,10,11}. C is complete; S has exactly edges 45 and 67; I is independent. C is complete to S and I is anticomplete to S. Between C and I the neighborhoods are

- N(8) ∩ C = N(9) ∩ C = {2,3};
- N(10) ∩ C = N(11) ∩ C = {0,1}.

Thus this is a strict 2K2-split graph, with c = i = 4. It has 12 vertices, whereas the conjectured order consequence is 2k + 3 = 11, and the literal clique bound demands c ≤ 2k − i − 1 = 3.

## Non-polarity, without relying on a source classification

A complete multipartite graph has no induced edge plus an isolated vertex. A cluster is P3-free; its independent sets have size at most its number of clique components.

Suppose (A,B) were an (∞,4)-polar partition. S cannot lie entirely in A, since 2K2 contains an edge plus an isolated vertex. If I were entirely in B, any vertex of B ∩ S together with the four vertices of I would give an independent set of size five in B, impossible. Choose u ∈ I ∩ A.

Since u is anticomplete to S, A cannot contain both endpoints of either S edge. Hence B meets both S edges; choose b1 and b2 in these two edges, respectively. They are nonadjacent. Any c ∈ C ∩ B would give the induced path b1,c,b2 in B. Thus C ⊆ A. But u has two nonneighbors in C; those two vertices are adjacent and together with u induce an edge plus an isolated vertex in A, again impossible. This proves non-polarity.

## All vertex deletions

For v ∈ C let {v,w} be its pair among {0,1},{2,3}, and let U be the two vertices of I nonadjacent to both members of that pair. In G − v set A = (C \ {v}) ∪ U and B = S ∪ (I \ U). A is complete multipartite: its parts are {w} ∪ U and the two singleton vertices of C \ {v,w}. B has the two S edges and two isolated I vertices, exactly four clique components.

For v ∈ I take A = C ∪ {4,5}, a clique, and B = {6,7} ∪ (I \ {v}), an edge and three isolated vertices, exactly four clique components.

For v ∈ S let E be the intact S edge and let z be the remaining vertex of its other edge. Take A = I ∪ {z}, an independent set, and B = C ∪ E, a clique.

These are actual partitions of each deleted graph. The property is hereditary by restricting a polar partition, so all proper induced subgraphs are polar. Consequently G is a minimal (∞,4)-polar obstruction and refutes the full universal assertion of MathDB 357910 through its c bound. The i bounds are not refuted. No minimal-order claim is made.

## Source fidelity and printed-object comparison

Both versions of arXiv:2303.17055 were retrieved. v2 Lemma 39 gives the standard definition-compatible criterion; Conjecture 49 on printed page 31 is exactly the bound in the literal normalized record. The actual 2026 journal article, Discrete Applied Mathematics 384, 229–242, DOI 10.1016/j.dam.2025.12.065, is author-uploaded at https://www.researchgate.net/publication/404357074_Polarity_on_H_-split_graphs. Its rendered primary body has Conjecture 37, page 242, with the same bounds. That body is accessible through the search tool, although direct publisher HTTP and direct author-page HTTP returned 403, and the tool's PDF link returned 404. No denied host was retried after its denial.

The arXiv figure inventory is Figure 1 (two partitions of C5), Figure 2 (graphs forbidden for membership in the 2K2-split class), and Figure 3 (two degree-equivalent 2K2-split examples with c = i = 4). Figure 3 was visually read in polar-figure3-correct.png and polar-figure3-detail.png. Both have I degrees 3,3,2,2; ours has I degrees 2,2,2,2, so neither is our graph. Figure 2 consists of graphs outside the required class and cannot be this strict 2K2-split witness. Figure 1 has five vertices. The journal has two figures: the membership obstructions and the degree-equivalent examples (renumbered Figures 1 and 2); its rendered text confirms the descriptions, but the journal figure pixels have not independently been retrieved. This remains a qualification, not an asserted complete visual clearance of that version.

The textual construction inventory includes pseudo-split obstructions (C5, not our 2K2 core), Proposition 27's monopolar obstructions, Remark 32's finite-s examples with i = 1, the H_s family preceding Theorem 38 with i = c − 2, Remark 47's c = 1 family, and the example after Conjecture 49 with c = k − 1. None has c = i = 4 and all I degrees two. The journal's analogous textual objects and theorem bodies in Sections 3–4 should be compared in independent review, including whether a broader printed family subsumes this witness. No claim of new-to-literature status is made.

The old polar exclusion is 350432, a uniqueness theorem for disconnected cograph minimal obstructions. It is not this bound: our graph is connected and its C–I subgraph contains an induced P4 (8,2,0,10), so it is not a cograph. Nevertheless the source-ingredient and small-modification exclusion standards still require root adjudication. The witness differs structurally from the source's post-conjecture near-complete C–I example: each I vertex now misses an adjacent pair and each missing pair has multiplicity two. This is the mechanism enabling a larger clique, not a numerical rounding or domain correction.

## Exact next Pi task

First independently verify the ordinary proof and finish the journal object-inventory/prior-art gate. If root regards the result as eligible, formalize this single 12-vertex graph; no search is needed. Use SimpleGraph (Fin 12), the source definition of a complete multipartite induced side (nonadjacency is an equivalence relation), and a cluster side supplied with at most four clique parts and no cross-part edges. Prove both graph-characterization bridges rather than postulating a checker interface.

An optional independent finite certificate has 66 adjacency bits, twelve A masks, and at most four B-component masks per deletion. Verify coverage, disjointness, all required adjacency/nonadjacency relations, and the full graph's non-polarity by the structural argument above. A 4096-subset exhaustive non-polarity check is possible but unnecessary; if used it must be a kernel-replayed Boolean lemma with a semantic bridge, not native_decide. Explicitly prove hereditary restriction to get the source minimality definition and finish the negation of the universal MathDB statement with k = 4, c = i = 4. Audit only propext, Classical.choice, Quot.sound, with no sorry, axiom, unsafe, admit or native_decide. All execution goes to Pi GLM, with at most two CPU cores, CPU 120 s / wall 140 s / sampled RSS 6 GiB per finite process. Do not formalize the toric-code lead for campaign credit without a separate eligibility ruling.
