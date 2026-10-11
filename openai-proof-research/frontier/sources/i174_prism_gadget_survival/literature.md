# I174 primary-literature search receipt

Date: 2026-10-10. Searches used the available WebSearch service with
`text=true`. The service returned short selections, abstract/interface text,
or metadata, **not readable full proofs**. No external theorem from these
searches is a dependency. No full-paper read or literature-priority claim is
made. The pinned OpenAI premises remain stipulated, irrespective of how
external pages describe Barnette's conjecture.

## Queries and returned leads

1. `Hamiltonian cycle polytope affine hull cubic bipartite planar graphs tight cut splicing Barnette Gorsky Steiner Wiederrecht`
   - *Matching Theory and Barnette's Conjecture*,
     https://arxiv.org/html/2202.11641 . Selection: a translation of
     Barnette's conjecture into matching theory; the retrieval included
     interface text, not a proof.
   - *Another Hamiltonian Cycle in Bipartite Pfaffian Graphs*,
     https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.26 .
     Selection cites Gorsky, Steiner and Wiederrecht, Discrete Mathematics
     346(2):113249 (2023).
   - Secondary leads: Wikipedia, Wolfram MathWorld, and a Radboud student
     survey. None is used as primary proof evidence.
2. `"Hamiltonian" "affine hull" "bipartite" polytope cubic`
   - *Facet-Hamiltonicity*, https://arxiv.org/pdf/2411.02172 and
     https://arxiv.org/html/2411.02172 ; also the authors' PDF at
     https://page.math.tu-berlin.de/~felsner/Paper/facet-ham.pdf .
     The selection concerns graph associahedra of complete bipartite graphs
     and caterpillars, a different problem.
   - MathOverflow, *Hamiltonian cycle polytope for the hypercube graph*
     (2018): https://mathoverflow.net/questions/299288/ .
     A question, not a primary theorem proving the present criterion.
3. `"Matching Theory and Barnette’s Conjecture" "4.16"`
   - https://arxiv.org/pdf/2202.11641 . Only bibliography-like text was
     returned. This is not an independent full reading of Theorem 4.16.
4. `"Hamiltonian cycle polytope" "dimension" bipartite`
   - The same MathOverflow hypercube question. No primary theorem matching
     the protected-survivor defect question was obtained.
5. `"Matching Theory and Barnette" Gorsky Steiner Wiederrecht tight cut cubic brace`
   - https://arxiv.org/pdf/2202.11641 : metadata identifies v3,
     15 August 2022.
   - Publisher abstract:
     https://www.sciencedirect.com/science/article/abs/pii/S0012365X22004551 .
   - *A Tight Lower Bound on Cubic Vertices and Upper Bounds on Thin and
     Non-thin edges in Planar Braces*, https://www.arxiv.org/pdf/2510.25188 .
6. `"Another Hamiltonian Cycle in Bipartite Pfaffian Graphs" authors 2024`
   - The Dagstuhl record above and https://arxiv.org/abs/2308.01574 .
     Returned metadata names Andreas Björklund, Petteri Kaski and Jesper
     Nederlof (2024); abstract selection concerns finding another cycle.
     No affine-survivor theorem was returned.
7. `"A Tight Lower Bound on Cubic Vertices" "Braces"`
   - https://arxiv.org/abs/2510.25188 ,
     https://arxiv.org/html/2510.25188v1 and the PDF above.
     Abstract selections discuss cubic vertices and bounds on thin edges
     in planar braces, not the seven-class survivor spaces here.
     A PDF selection mentions thin edges and tight cuts. No full proof read.

## Actual pinned source read

Local authenticated bytes:
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`,
`cor:pfaffian-paths`, lines 812–828 (surrounding material 780–838).
The actual statement concerns finite simple cubic 3-vertex-connected
bipartite Pfaffian graphs and every prescribed three-edge path; it explicitly
includes the planar class. No upstream truth audit was performed.

The immutable contract is `sources/upstream.json`, commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Catalogue family 180 and the
complete `sources/preprints-tree.json` identify the single matching family
manuscript at
`preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/`.
The tree includes its README, build sources, references, and paper PDF;
no second companion manuscript in this family was identified.
No new remote manuscript was downloaded.

## Novelty assessment

The splice bijection, rank-nullity, and affine fibre-product argument are
elementary and overlap the project's earlier I165/I172 machinery. The
explicit protected-survivor defect criterion and its four reduced exterior
certificates are new calculations in this iteration, not demonstrated
new-to-literature theorems. The search is limited and does not establish
priority or absence of prior art.
