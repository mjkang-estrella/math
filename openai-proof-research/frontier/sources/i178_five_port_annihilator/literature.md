# I178 source and primary-literature scope

Date: 2026-10-11. No literature-priority claim.

The immutable `sources/upstream.json` contract specifies OpenAI/math revision
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Every theorem there is stipulated
true. Catalogue family 180 and its paths in the complete
`sources/preprints-tree.json` were inspected. That family lists one manuscript,
not a separate companion affine-dimension theorem.

Actual pinned source read:
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`,
introduction and `thm:main`, `cor:edge-avoidance`, and
`cor:pfaffian-paths`, including the hypotheses and adjoining explanation.
The last statement assumes finite, simple, undirected, cubic,
3-vertex-connected, bipartite, Pfaffian graphs and extends a prescribed
three-edge path to a Hamiltonian cycle. Planar graphs are explicitly included.
This is not a typed affine-fullness theorem. I178's linear identities and
finite certificates need no stronger source statement.

Pinned provenance, not a fresh retrieval:
https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/build/paper.tex

## Searches actually made

1. `"Matching Theory and Barnette's Conjecture" "4.16"`

   Primary result: https://arxiv.org/pdf/2202.11641.
   The returned text was a brief reference-list selection, beginning
   “Solution of Barnette's Conjecture. Journal of Graph Theory,
   96(2):269–288, 2021.” It was not the full statement or proof of 4.16.
   No new external theorem is inferred from that selection.

2. `Hamiltonian cycle polytope affine hull fixed boundary path packing graph connection matrix`

   Primary leads included *Facet-Hamiltonicity*:
   https://par.nsf.gov/servlets/purl/10671111 and
   https://page.math.tu-berlin.de/~felsner/Paper/facet-ham.pdf.
   Returned abstract snippets concern cycles in polytope skeletons meeting
   facets, not the affine hull of the graph's Hamiltonian-cycle incidence
   vectors. These do not supply the missing local-fibre realization theorem.
   MathOverflow, Math StackExchange and Wikipedia results also appeared;
   none was treated as primary proof evidence.

3. `"Another Hamiltonian Cycle in Bipartite Pfaffian Graphs"`

   Primary leads:
   https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.26
   and https://arxiv.org/abs/2308.01574.
   Returned snippets describe algorithms for finding another Hamiltonian
   cycle, including linear-time and logarithmic-space results. They do not
   establish completeness or affine fullness of prescribed five-port fibres.
   The truncated storage-PDF link was not treated as a completed retrieval.

Full-text search was requested, but only the returned selections were read.
No full external primary proof was downloaded or read this round. The
inherited I177 literature receipt remains strictly bound. The four-relation
presentation is an exact project calculation in elementary linear algebra;
its new-to-literature status is not established. No contribution-gate
clearance is claimed, and the substantive realization boundary remains open.
