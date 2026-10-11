# I179 source and literature receipt

Date: 2026-10-11. This is a research-lead receipt, not priority clearance.

## Stipulated primary source actually read

Immutable upstream revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
Read `sources/upstream.json`, family 180 of `sources/CONTENTS.md`,
the complete family entries in `sources/preprints-tree.json`, and the actual
statements in the retained, strictly authenticated
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`.

Pinned provenance:
`https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/build/paper.tex`

This iteration read the existing pinned manuscript bytes; it did not perform
a new network retrieval or audit upstream truth.

- `thm:main`: every finite simple undirected cubic bipartite planar
  3-vertex-connected graph is Hamiltonian.
- `cor:edge-avoidance`: every edge in such a graph can be avoided by a
  Hamiltonian cycle.
- `cor:pfaffian-paths`: every three-edge path in a finite simple undirected
  cubic 3-vertex-connected Pfaffian bipartite graph extends to a Hamiltonian
  cycle. Planarity is sufficient for the Pfaffian hypothesis in the source.

The catalogue and complete manuscript-path listing show one manuscript for
this result family, not a companion theorem asserting affine fullness or
weighted packing recombination. Other manuscripts with “Hamiltonian” in
their titles concern symplectic Hamiltonians, not this graph problem.
The present finite obstruction and its elementary two-colour proof do not
require an additional upstream theorem.

## External primary-literature search, exact read limits

Searches used the available web-search tool with `text=true`. Despite that
request, the returned material was short selected excerpts, not complete
papers. No external proof was read in full. No claim below relies on an
unread proof.

Queries, in order:

1. `Gorsky Steiner Wiederrecht 2023 Barnette conjecture Pfaffian braces P4 Hamiltonian Theorem 4.16`
2. `Hamiltonian cycle polytope affine hull cubic bipartite planar graphs alternating path exchange spanning path packings`
3. `"Another Hamiltonian Cycle in Bipartite Pfaffian Graphs" algorithm alternating cycle 2024`
4. `"Another Hamiltonian Cycle in Bipartite Pfaffian Graphs" "edge" "linear"`
5. `"Matching Theory and Barnette" "4.16" "path"`
6. `"Another Hamiltonian Cycle" "Pfaffian" "containing" "edge" Björklund Kaski Nederlof`

Primary leads returned:

- Maximilian Gorsky, Raphael Steiner, Sebastian Wiederrecht,
  *Matching Theory and Barnette's Conjecture*,
  Discrete Mathematics 346(2), 113249 (2023).
  <https://arxiv.org/abs/2202.11641>
  <https://arxiv.org/html/2202.11641>
  <https://arxiv.org/pdf/2202.11641>
  The search selected the beginning of Theorem 4.16 (“The following
  statements are equivalent”) and a reference to its P4-Hamiltonian
  conclusion. That is a lead, not a new reading of its proof. The prescribed
  path statement used here is the already-read stipulated upstream corollary.
- Andreas Björklund, Petteri Kaski, Jesper Nederlof,
  *Another Hamiltonian Cycle in Bipartite Pfaffian Graphs*,
  ICALP 2024, LIPIcs 297, article 26.
  <https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.26>
  <https://arxiv.org/abs/2308.01574>
  Excerpts mention linear-time and logarithmic-space algorithms for
  bipartite Pfaffian graphs of minimum degree three when supplied an
  existing Hamiltonian cycle, and the zero-or-at-least-six-cycle
  consequence for cubic bipartite Pfaffian graphs. The exact algorithm,
  every input parameter, and its proof were not read. In particular this
  receipt does not claim it preserves a fixed exterior, pairings, or a
  prescribed sum of packing incidence vectors.

The broad affine-hull query also returned secondary Hamiltonian-path pages,
a Barnette survey page, an enumeration lead, and an unrelated
facet-Hamiltonicity paper. None supplied a proof of L179.

## Consequence for this assignment

Existence of a Hamiltonian cycle through three edges is not control of
the entire edge-multiplicity vector of two or three given packings.
Likewise brace matching extension is not an acyclic-spanning-complement
theorem. No external result is promoted to either assertion.

The literature search does not establish that the local obstruction or
the conditional recombination formulation is new to the literature.
L179 remains unresolved; no ninth finding is nominated.
