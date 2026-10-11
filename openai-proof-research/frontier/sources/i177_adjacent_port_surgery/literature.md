# I177 primary-literature comparison and source-read scope

Date: 2026-10-11. No priority claim or literature clearance.

## Stipulated pinned source

`sources/upstream.json` fixes OpenAI/math at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Catalogue family 180 is
*Paired states and Hamiltonian cycles in cubic bipartite planar graphs*.
The complete `sources/preprints-tree.json` lists that manuscript's
`README.md`, `build/paper.tex`, `build/references.bib`,
`build/triangle-figure.tex`, and `paper.pdf`. No companion graph-theory
manuscript for that family is listed there. Unrelated symplectic
Hamiltonian titles are not companions.

Actual local pinned text read:
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`,
`thm:main`, `cor:edge-avoidance`, and `cor:pfaffian-paths` (812–828).
The last statement requires a finite simple undirected cubic,
3-vertex-connected, Pfaffian bipartite graph and extends every
three-edge path to a Hamiltonian cycle; the text explicitly includes
planar graphs. The inherited A175 argument needs those hypotheses.
I177's finite ranks, path products, and matching certificates do not
require an upstream truth audit or a stronger extension theorem.

Pinned provenance URL (not a new network retrieval):
https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/build/paper.tex

## Searches actually performed

1. `Hamiltonian cycle polytope affine hull cubic bipartite planar graphs braces Gorsky Steiner Wiederrecht 2023 tight cuts`
   - Gorsky, Steiner, Wiederrecht, *Matching Theory and Barnette's
     Conjecture*, arXiv:2202.11641; published Discrete Mathematics
     346(2), 113249 (2023). Primary links:
     https://arxiv.org/abs/2202.11641 and https://arxiv.org/pdf/2202.11641.
     Returned abstract/snippets describe a matching-theoretic
     translation of Barnette's conjecture.
   - *Another Hamiltonian Cycle in Bipartite Pfaffian Graphs*,
     ICALP 2024, https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.26.
     The returned selection includes the GSW bibliographic reference.
   - *A note on the 2-factor Hamiltonicity Conjecture*,
     https://arxiv.org/html/2408.08128v2. A reference-list selection,
     not a proof read.
   - A Wikipedia result also appeared; it is not primary evidence
     and does not override the stipulated source contract.

2. `"Hamiltonian" "affine hull" "cubic"`
   - Primary-title lead: *Approximations of the Convex Hull of
     Hamiltonian Cycles for Cubic ...*, Flinders Hamiltonian Cycle
     Project. The tool returned a truncated URL
     `http://sites.flinders.edu.au/flinders-hamiltonian-cycle-project/wp-content/up...`
     and an introductory NP-completeness snippet. The full URL,
     authors, exact theorem, and proof were not obtained.
   - *Hamilton Cycles in Cubic Graphs*,
     https://www.tandfonline.com/doi/pdf/10.1080/09728600.2007.12088840.
     Only a keyword/definition selection was returned.
   - Generic affine-hull reference pages were not used.

3. `"Matching Theory and Barnette's Conjecture" "brace" "4.16"`
   - The arXiv PDF lead above returned a brief passage mentioning
     brace checks, not the full proof of Theorem 4.16.

Although full-text search results were requested, the returned selections
are **not full primary proof reads**. No downloaded paper or complete
proof is claimed. The comparison establishes relevant prior frameworks,
not novelty of rational rank-nullity, five-port products, or the present
finite obstruction. The exact adjacent surgery is new to this authorized
project sequence; new-to-literature status is unestablished.
