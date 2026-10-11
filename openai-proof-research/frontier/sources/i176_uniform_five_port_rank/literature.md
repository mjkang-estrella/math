# I176 literature receipt, 2026-10-10

These are actual WebSearch queries and returned selections, not claims to
have read full primary proofs. No browser, outbound file upload, or upstream
truth audit was used. The local pinned manuscript statement was read separately.

1. `Hamiltonian cycles affine hull prism graphs path packing five edge cut polytope dimension`
   returned mostly irrelevant results about **facet-Hamiltonicity** (a different
   notion), including Akitaya, Cardinal, Felsner et al.,
   https://arxiv.org/html/2411.02172 and
   https://par.nsf.gov/servlets/purl/10671111.
   Returned selection: “facet-Hamiltonian cycles of polytopes, defined as cycles
   in their skeleton such that every facet is visited exactly once.”
   This does not establish a result about our survivor affine hull.
2. `Gorsky Steiner Wiederrecht 2023 Pfaffian graphs P4 Hamiltonian Theorem 4.16 Barnette`
   returned the primary paper **Matching Theory and Barnette's Conjecture**,
   https://arxiv.org/pdf/2202.11641, with metadata
   `arXiv:2202.11641v3 [math.CO] 15 Aug 2022`, and
   https://www.sciencedirect.com/science/article/abs/pii/S0012365X22004551.
   It also returned **Another Hamiltonian Cycle in Bipartite Pfaffian Graphs**,
   https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.26,
   whose selection cites Gorsky, Steiner, Wiederrecht, Discrete Mathematics
   346(2):113249 (2023).
3. `"Hamiltonian" "affine hull" "bipartite" polytope dimension`
   returned the unrelated facet-Hamiltonicity paper and secondary questions
   about Hamilton path and hypercube cycle polytopes. Those secondary questions
   are not used as mathematical premises or novelty clearance.
4. `site.arxiv.org "Matching Theory and Barnette" "4.16"`
   returned the primary PDF above, with the selection
   “Theorem 4.16. The following statements are equivalent: ... Proof. The
   equivalence of (i) and (ii) can be taken from Lemma 1.2. ... Corollary 4.9.
   (We note that the Heawood graph is also P4-Hamiltonian...)”.
   This is a **snippet**, not a full reading of that equivalence proof.
5. `"Hamiltonian cycle polytope" "prism"`
   returned https://dmtcs.episciences.org/2079/pdf,
   **Hamiltonian decomposition of prisms over cubic graphs**, and the primary
   journal page
   https://www.sciencedirect.com/science/article/pii/S0012365X04002122,
   **Hamiltonian decompositions of prisms over cubic graphs**.
   The selection defines Hamiltonian decomposition and discusses prisms over
   simple 3-polytopes. It does not state the five-port survivor-rank result.
   The search also returned the secondary problem page
   https://dwest.web.illinois.edu/regs/hamprism.html.

## Pinned source actually read

`sources/upstream.json`: OpenAI/math revision
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
Catalogue entry 180 and the matching subtree of the complete
`sources/preprints-tree.json` identify one manuscript family:

`preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/build/paper.tex`.

Pinned source location:
https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Paired-states-and-Hamiltonian-cycles-in-cubic-bipartite-planar-graphs-September-24-2026/build/paper.tex

The authenticated local copy
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`,
lines 812–828, states `cor:pfaffian-paths`: every three-edge path in a
finite simple cubic 3-vertex-connected bipartite Pfaffian graph lies in
a Hamiltonian cycle, including the planar case. This remains stipulated
true. It supplies the inherited A175 statement, not an assumption needed
by I176's explicit packing proof. The catalogue/path check found no
separate companion manuscript in this result family; it is not an
exhaustive literature duplicate search.

## Novelty boundary

No returned selection supplies or rules out the explicit determinant
`4-k` and fixed 9-by-9 minor for this exact surgery. That is not proof of
literature novelty. The result is a new-to-project family obstruction
with no literature-priority claim, no independent review clearance and
no ninth accepted finding.
