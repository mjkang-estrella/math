# 352253: held doubled-cubic counterexample

This is a proposed ordinary finite refutation, not an accepted discovery and not a completed literal Lean endpoint. Root must adjudicate statement fidelity, significance, source-ingredient overlap and novelty before further investment. The direct Lean minimality computation was stopped at approximately 5.9 GB RSS. No acceptance credit is claimed.

The exact target is Jeffries–Yeats, Conjecture 5.1, journal pp. 678–679, Definition 2.1 for the transformations. The current arXiv PDF and the actual journal PDF retain the conjecture. The source explicitly allows coinciding vertices in its illustrated reducible subgraphs, provided the edges remain distinct. That convention must be retained in an independent fidelity review.

Use the zero-based adjacency matrices in `outputs/delta-trace-checked.json`. The original graph is the doubled simple cubic graph with edges

```
03 06 0-14 12 19 1-16 25 2-16 37 3-14
46 4-12 4-15 59 5-13 6-11 78 7-11 8-10 8-17
9-12 10-11 10-14 12-15 13-16 13-17 15-17
```

Here the compact `03` means the pair (0,3), not an integer label. The unambiguous pair list is in `outputs/delta.json`, n = 18, trial = 0. All original vertices have degree 3, and the simple graph is connected and non-bipartite.

Pure YY–Delta reductions at current indices `[0,0,3,4,6,7,11]` produce an 11-vertex graph Gprime. This is a smallest result of *all* purely reducing sequences, not merely a maximal independent-set heuristic. The complete reduction DAG has 2328 labelled matrix states and 9846 arcs. Every node has order at least 11. The root is the original doubled graph, and every legal YY–Delta successor of every state appears as an arc. Closure therefore proves by induction on any reduction sequence that its terminal order is at least 11. The displayed seven reductions attain 11. `verify_dag.py` checks the complete closure using an implementation separate from the search's graph update code.

The endpoint vertices for a Figure 14 chain in Gprime are 3 and 6: each has two single and two double connections. Possible internal connecting vertices are 4, 5 and 7: each has four single connections and one double connection. Among these eligible base vertices, the only single-edge triangles connecting eligible bases are `(4,7,9)` and `(5,7,9)`. In particular, no chain can even leave either endpoint. This obstruction allows vertex coincidences further along a chain: its first triangle is already impossible. The semantic bridge from the source's verbal and illustrated chain to these necessary incidence conditions is ordinary reasoning here and still requires independent fidelity review and a Lean proof.

Nevertheless, perform these nine operations, always on the current zero-based labels:

```
expand triangle (0,5,7)
expand triangle (1,6,8)
reduce vertex 6
reduce vertex 10
expand triangle (4,7,10)
expand triangle (3,7,10)
reduce vertex 10
reduce vertex 7
reduce vertex 9
```

The result has 10 vertices. Every intermediate matrix is symmetric, loopless and 6-regular; every expansion uses three distinct vertices with positive triangle edges; every reduction removes a vertex with exactly three double connections. Thus Gprime is not minimal in its equivalence class. Together with the two preceding facts, this contradicts the claimed chain criterion, subject to the stated source-chain fidelity bridge.

`lean/Delta153.lean` strictly compiles with Lean 4.34.1 and the pinned read-only mathlib cache. It proves the explicit nine-move reachability, the strict order drop and an endpoint-blocking Boolean fact using kernel `decide`. Its displayed axioms are only propext. `lean/Soundness.lean` proves soundness of the recursive pure-lower-bound checker for arbitrary pure reducing sequences; displayed axioms are propext and Quot.sound. `PureCheck.lean` is an **unproved computation attempt**, not a theorem available for use: its recursive `decide` expansion was stopped near the RSS cap. Do not import it as a certificate.

Remaining formal work: replace that exponentially duplicated computation by the supplied memo DAG certificate, prove its generic closure-checker soundness, certify the DAG with bounded module sizes, prove the source-chain semantic bridge (including possible vertex coincidences), certify the initial doubled-cubic hypotheses, and assemble the negation of the literal source conjecture. Full local declaration/axiom audit and fresh extracted strict replay also remain. No full upstream rebuild is claimed.

Bounded prior-art check: current OpenAI/math and Omega heads and complete preprints/D5/Problems trees are saved. No Jeffries–Yeats/delta–YY path-level counterpart was found. Web searches for the authors, Conjecture 5.1 and doubled-cubic counterexamples returned the source rather than a resolution. This is not a universal novelty clearance. The source's own Figure 14 already contains several non-chain reducible gadgets: whether the present original doubled graph plus the pure-minimum certificate is substantive beyond those ingredients is a root-review question. Do not silently clear that objection. No author contact or publication occurred.
