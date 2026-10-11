# I175 literature and pinned-statement reading receipt

Search date: 2026-10-10. Searches used the available web-search service
with text requested. It returned short selections, not complete articles.
No downloaded or ancestor executable was run. No outside result from this
search is a mathematical dependency or a novelty certificate.

## Queries and returned primary-source leads

1. `Hamiltonian cycle polytope cubic graph 3 edge cut dimension affine span splice prism`

   - *Hamiltonian decompositions of prisms over cubic graphs* (2004),
     https://www.sciencedirect.com/science/article/pii/S0012365X04002122
     and https://dmtcs.episciences.org/2079/pdf.
     The selection describes the Alspach–Rosenfeld conjecture about a
     decomposition of a prism over a 3-connected cubic graph into two
     Hamiltonian cycles. This is not the present cubic even-cycle prism
     survivor-affine-dimension problem.
   - *Facet-Hamiltonicity*,
     https://par.nsf.gov/servlets/purl/10671111.
     The selection concerns cycles visiting polytope facets, not the
     affine span of graph Hamiltonian incidence vectors.
   - Non-primary Stack Exchange and Wikipedia results were not proof inputs.

2. `Gorsky Steiner Wiederrecht 2023 Hamiltonian cycles Pfaffian cubic bipartite P4 Hamiltonian`

   - *Another Hamiltonian Cycle in Bipartite Pfaffian Graphs*,
     https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.26.
     The returned selection cites Gorsky, Steiner and Wiederrecht,
     *Matching theory and Barnette's conjecture*, Discrete Mathematics
     346(2):113249 (2023).
   - That primary paper's publisher page:
     https://www.sciencedirect.com/science/article/abs/pii/S0012365X22004551.
     The selection states that it translates Barnette's conjecture into
     matching theory. The full proof was not returned or read.
   - *A note on the 2-factor Hamiltonicity Conjecture*,
     https://arxiv.org/abs/2408.08128 and
     https://arxiv.org/html/2408.08128v2.
     The selection discusses cubic bipartite graphs all of whose
     2-factors are Hamiltonian, a different restriction.

3. `"Hamiltonian" "polytope" "dimension" "cubic" "3-cut"`

   - Further *Facet-Hamiltonicity* selections at
     https://page.math.tu-berlin.de/~felsner/Paper/facet-ham.pdf and
     https://arxiv.org/pdf/2411.02172.
   - Gil Kalai, *Polytope skeletons and paths*,
     https://www.csun.edu/~ctoth/Handbook/chap19.pdf.
     Only a short selection about polytope graphs was returned.
   - A Wikipedia Barnette entry was not used to establish an assertion.

These searches did not locate a full primary proof of the exact
five-port survivor-kernel criterion. That does NOT establish absence
from the literature. The criterion is elementary linear algebra and
path-packing gluing; no priority or substantiality claim is made.

## Actual pinned source statement read

The repository's `AGENTS.md`, `sources/upstream.json`, catalogue family
180, and complete `sources/preprints-tree.json` path listing identify
one manuscript in that result family:

`preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/build/paper.tex`

Pinned raw source:
https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/build/paper.tex

The authenticated local source is
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`,
SHA-256 `03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56`.
Lines 812–828, `cor:pfaffian-paths`, were read, including its actual
hypotheses: finite simple undirected, cubic, 3-vertex-connected,
Pfaffian and bipartite. Every three-edge path extends to a Hamiltonian
cycle. The source explicitly includes the planar case.

The complete catalogue/tree check finds no second companion manuscript
under result 180. This is not an exhaustive search through unrelated
families. All pinned OpenAI theorems are stipulated true, not audited.
