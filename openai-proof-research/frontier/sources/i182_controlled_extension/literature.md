# I182 source and literature receipt

2026-10-11. No upstream truth audit and no literature-priority claim.
All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are
stipulated true.

## Pinned source actually read

Read `AGENTS.md`, `sources/upstream.json`, catalogue family 180 in
`sources/CONTENTS.md` (Barnette's Hamiltonian-cycle conjecture; the
P4-Hamiltonicity equivalence is stated in the catalogue entry itself),
and the complete family path listing in `sources/preprints-tree.json`.
The family contains only the manuscript
`Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026`;
no companion prescribed-two-edge or packing-reconfiguration theorem is
listed there.

Read the actual pinned statement and proof text in
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`:

- `thm:main`: every finite simple undirected cubic bipartite planar
  3-vertex-connected graph has a Hamiltonian cycle;
- `cor:edge-avoidance`: every edge of such a graph is avoided by some
  Hamiltonian cycle (proof: prescribe the dual facial edge);
- `cor:pfaffian-paths`: every path on four vertices (three edges) in a
  finite simple cubic 3-vertex-connected Pfaffian bipartite graph lies
  in a Hamiltonian cycle, via Gorsky–Steiner–Wiederrecht
  [Theorem 4.16]; planar graphs are Pfaffian [Theorem 4.6].

These are one-path or pure existence statements. None prescribes two
disjoint edges simultaneously on a Hamiltonian cycle, controls a
matching complement's component pairing, or forces a surviving
five-port type. No result in the I182 report relies on an unread
external proof. No new external search was performed or used.

## Prior research actually read

Read the complete finalized I182 brief and dispatch record; I181's full
brief, report, analytic attempt, failures ledger and parent
disposition; the I181 parent precheck, verification, certificate,
replay and integration receipts (all bound in the freeze); and the
I176–I180 reports relevant to the mandated controls. The I181 report,
seal and verifier hashes authenticate against the supplied detached
anchors exactly. Ancestor Python remains opaque hashed evidence: read
only for retained certificate schemas and value interpretation, never
executed, imported, compiled or copied as implementation.
