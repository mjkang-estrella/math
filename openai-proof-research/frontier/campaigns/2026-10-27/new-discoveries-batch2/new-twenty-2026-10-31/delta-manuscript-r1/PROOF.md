# Proof dossier — DRAFT, AI-assisted, unaccepted

Target: MathDB 352253, Jeffries–Yeats Conjecture 5.1, journal p. 678. The result is a refutation under the illustrated, edge-distinct capacity reading of Figure 14(a), (b), (d), allowing apex and attachment coincidences. This qualification is essential. Zero accepted credit; root alone accepts.

## Hypotheses and explicit witness

Use exactly the base edge list and doubled adjacency matrix in paper.md, section 3, and recomputation.json. Each row of the simple base has three distinct neighbours; doubling gives a finite loopless undirected 6-regular multigraph. There is no appeal to a generic cubic-graph existence statement.

The pure current-index reductions are [0,0,3,4,6,7,11]. Each centre row has precisely three positive entries, each equal to 2. Deleting it and adding one edge per neighbour pair gives the next matrix in pure_matrices. The terminal H has order 11.

## Global pure lower bound

The fresh checker reconstructs all reachable canonical labelled matrices from the explicit edge list using Definition 2.1. It enumerates 2,328 distinct states and 9,846 legal-centre arcs. The order distribution is recorded in recomputation.json. It checks every supplied child arc, its centre, exact successor matrix, full centre census, root and equality of the independently reached set with the supplied certificate. Every state has order at least 11. Induct on any pure path: the root is in this finite set and every legal successor remains in it. Thus the terminal order is at least 11. Increasing survivor numbering loses no graph up to relabelling. In Lean, Transport.canonical_transport discharges the arbitrary-numbering bridge. The displayed path attains the bound, so H is a pure minimum.

## Literal chain absence

An end base has ambient row type [1,1,2,2]. In H only 3 and 6 qualify. Their single neighbours are 1 and 8, joined by a triple connection. The first triangle must use these three vertices, since both end double attachments are reserved. Neither 1 nor 8 is another end. To continue through either, its double attachment must use the two remaining edges of the triple pair 1–8.

Starting from 6 leaves forward candidates 3,4 with no edge between them. Starting from 3 leaves candidates 4,6. After a second triangle, neither candidate has an available double attachment: 4 has only residual single connections, and 6's double connection to 3 has already been reserved at the start. Vertex 4 cannot be an end; termination at 6 would reuse its consumed double attachment to 3. Exchange 1 and 8 for the other orientations. This exhausts all prefixes and all lengths, without restricting internal row types. It proves no capacity-based chain occurs. A complete fresh residual-capacity search confirms absence in all 25 minima and succeeds on an alias control with an internal triple connection.

## Nonminimality

The witness is expand (1,6,8); reduce 6; expand (4,7,10); expand (3,7,10); reduce 10; reduce 7; reduce 9. Current orders: 11,12,11,12,13,12,11,10. Expansion appends a vertex; reduction closes the numbering gap. Every expansion triangle has positive entries, every removed centre has the exact row required by Definition 2.1, and each resulting graph remains loopless, symmetric and 6-regular. Thus H is equivalent to an order-10 graph and is not minimal. Global minimality at order 10 is neither needed nor claimed. Chain-free implying minimal is false for this pure minimum, disproving the biconditional.

## Figure 14, interpretation, and significance limits

The initial H contains none of the seven printed gadgets under the checked template reading. The shorter witness exposes (c) after one expansion, but not (g) at that point. The original nine-move trace exposes both (c) and (g) after two expansions, with a commuting inverse detour removed in the shorter trace. Fresh embeddings are in recomputation.json. This corrects the brief's compressed timing language explicitly. These gadgets were already known to the source; the missing doubled-input/pure-minimum restriction is the finite counterexample's content. Significance is qualified and modest. There is no new simplification theory or priority claim.

## Formal endpoint and inherited receipts

lean-source.zip is byte-identical to delta-formal-r3/source.zip, SHA-256 c0dba5dc4f6738531b09750bd5e6f46ba565ba952f50fbe927e4f9cfe4a0e08c. Endpoint: Round2.literal_negation : ¬ Literal.Conjecture51. This task executes no Lean, lake or leanchecker. The source packet has 634 Lean modules, including 582 four-node closure chunks. Exact matrix checks, generic certificate soundness, canonical transport, literal chain absence, doubled-cubic hypotheses and the explicit descent are assembled into the unconditional endpoint.

The round-two independent fidelity review held the full replay after Closure276 exceeded the internal memory cap. It qualified definitions under the illustrated reading and passed bridges and independent numerical checks. Round three split census proofs and narrowed imports without changing graph data or original statements. The root's subsequent hash-bound replay-result.json records PASS for its fresh complete replay, explicit-module leanchecker, clean source/metadata audit and only propext, Classical.choice, Quot.sound as endpoint dependencies. These are inherited evidence, not a replay performed here. No full upstream rebuild or formal edge-ID API equivalence theorem is asserted. Bounded prior-art search receipts do not prove worldwide novelty. Root decides acceptance.
