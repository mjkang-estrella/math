# I180 source reading and literature limits

2026-10-11. No literature-priority claim and no upstream truth audit.
All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
are stipulated true.

## Pinned primary source

Read `AGENTS.md`, `sources/upstream.json`, the complete relevant catalogue
entry 180 in `sources/CONTENTS.md`, and all seven family paths in the
complete `sources/preprints-tree.json`, not the truncated root-tree cache.
The catalogue has one manuscript in this family. It does not list a
companion affine-fullness or packing-reconfiguration theorem.

Read the actual statements and surrounding explanations of `thm:main`,
`cor:edge-avoidance`, and `cor:pfaffian-paths` in the authenticated
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`.
The corollary proofs were in the inspected passages. This is not a claim
to have reread the whole upstream proof.

Pinned provenance:
https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/build/paper.tex

The main theorem supplies Hamiltonicity for finite simple undirected
cubic bipartite planar 3-vertex-connected graphs. Edge avoidance is
quantified over each edge of such a graph. The prescribed-path corollary
requires finite simple undirected cubic 3-vertex-connected bipartite
Pfaffian graphs, and extends every three-edge path to a Hamiltonian cycle.
Planarity suffices for the Pfaffian condition in the source.
These statements are not prescribed exterior-fibre or edge-sum theorems.
This iteration used retained pinned source bytes, not a fresh download.

Also read the full finalized I180 and original I179 briefs, full I179
report and finalized parent disposition, dispatch archive and final
integration receipt, full U176, I177 and I178 reports, I178 parent
disposition, and relevant R168/F169/R170 definitions in the original
reports. Ancestor Python was hashed only, not used as implementation.

## External searches actually performed

The web-search tool was used with `text=true`. Its responses were short
selected excerpts, not full papers. No external proof was read in full.
No result in the I180 report relies on an unread external proof.

Queries, in order:

1. `"Another Hamiltonian Cycle in Bipartite Pfaffian Graphs" alternating cycle prescribed edge`
2. `"Matching Theory and Barnette" "4.16" "Hamiltonian"`
3. `"Another Hamiltonian Cycle in Bipartite Pfaffian Graphs" "Theorem 1" "edge"`
4. `Hamiltonian paths reconfiguration alternating cycle flip connected planar cubic bipartite prescribed endpoints`

Primary leads:

- Björklund, Kaski, Nederlof, *Another Hamiltonian Cycle in Bipartite
  Pfaffian Graphs*, ICALP 2024.
  https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.26
  https://arxiv.org/abs/2308.01574
  Excerpts describe algorithms taking a bipartite Pfaffian graph of
  minimum degree three and an existing Hamiltonian cycle. A further
  excerpt mentions at least three other Hamiltonian cycles through an
  edge of a Hamiltonian cycle. Full statements, algorithms, and proofs
  were not retrieved/read. No prescribed helper conclusion is inferred.
- Gorsky, Steiner, Wiederrecht, *Matching Theory and Barnette's Conjecture*.
  https://arxiv.org/pdf/2202.11641
  The search excerpt identifies Theorem 4.16 and its equivalent
  statements, and mentions the Heawood graph's P4-Hamiltonicity.
  This is not a reading of the proof of that equivalence; the source
  used for prescribed paths is the already-read stipulated corollary.
- *Reconfiguration of Hamiltonian paths on grid graphs*,
  https://arxiv.org/html/2601.06749v1
  Only a title/content-selection excerpt was returned. Its hypotheses,
  moves, and proof were not read.
- *Shortest Reconfiguration of Perfect Matchings via Alternating Cycles*,
  https://epubs.siam.org/doi/abs/10.1137/20M1364370
  Only an abstract-level excerpt about shortest alternating-cycle
  reconfiguration was returned. Perfect-matching reconfiguration does
  not establish that complementary spanning path packings remain acyclic
  or preserve the prescribed five-port pairing.

The broad query also returned a Wikipedia page and a secondary review of
flip graphs of almost-perfect matchings. Neither is treated as a primary
proof or as novelty clearance.

## Consequence

No read theorem gives a spanning same-type helper containing every
required alternating-cycle half, excluding the other half, and retaining
its pairing and acyclicity after the exchange. The finite five-vertex
helper graph is not claimed new to the literature or substantial enough
to increment acceptance.
