# Unaccepted ordinary candidate352972

Let $G$ be a flat graph, and let $c_i(G)$ denote the number of $i$-cliques in $G$. Define

$$
D_{clique}(G)=\left|\sum_{i:\ i\ \mathrm{is\ odd}}c_i(G)-\sum_{i:\ i\ \mathrm{is\ even}}c_i(G)\right|.
$$

Call $G$ **balanced** when $D_{clique}(G)\leq 1$.

**Balanced-graph conjecture.** Any flat graph is a balanced graph.

The source notes that related subclasses of flat graphs satisfy $D_{clique}(G)=1$. The supplied text gives no resolution of the conjecture, so it remains open.

Source: Teimoori Faal, arXiv2112.09721v1, Definition2.2 and Conjecture2, actual full text read. Current metadata lists v1 only, no DOI/journal reference. Body and metadata hashes are in SHA256-MANIFEST.json; literal/raw/chunk hashes in keyedresults.json.

Full witness, every graph hypothesis, all clique counts and both c0 interpretations are proved in ORDINARY.md, section352972. K3,3 has vertices L1,L2,L3,R1,R2,R3 and all nine cross edges. It is connected and triangle-free, hence every edge belongs to0<=2 triangles. Its clique counts are c0=1,c1=6,c2=9,c_i=0 for i>=3, giving D4 (or3 excluding c0), contradicting D<=1. No primary planarity or no-isolated-edge hypothesis is silently added.

This is an exact source/literal ordinary refutation, with no earlier printed exact counterexample established. Actual source reading and bounded current searches are documented; neither exhaustive novelty nor substantive significance is established. Independent source-fidelity/significance/prior review remains required. Smallness alone is not an exclusion rationale. No formal execution or acceptance. Credit0;52/60 unchanged.
