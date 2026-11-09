# r2 research notes

The predecessor's large search and coefficient generation were not rerun. All writes stayed in coxeter-spectral-r2. No subagents, git, shared edits, messages, publication, or browser tabs.

Primary-first comparison: downloaded McKay1977, actual Godsil2007 cited slides, and supplemental Godsil–McKay1982 from author hosts. Read theorem bodies and proof mechanisms as scoped in source-comparison.md, not merely abstracts. Compared later Marjanski et al numbered graph products: Thm4.9 still imports the graph-product shuffling lemma; Thm5.14 is link-regular and cannot provide this irregular-tree refutation. Root still must independently review novelty.

Formal work:
- Constructed actual finite simple graphs; explicit paths certify connectivity and card(edgeSet)=18 gives treehood via pinned library theorem.
- Computed rational Krylov intertwiners from the EXISTING fixed pair (not a search for graphs). Standard basis cyclic vectors failed several times; deterministic small random vectors produced full rank for each pair. `make_similarity.py` reproduces the selected witnesses. Actual P,Q arithmetic is checked by Lean, so correctness does not depend on SymPy or its characteristic-polynomial algorithm.
- Whole-matrix and fin_cases-on-both-indices decision proofs exhausted 2300/3500MB memory. Rowwise quantified decision proofs succeeded under3500MB; successful spectral build136.2s,2 Lean workers. Failed earlier diagnostics are retained in logs and are not certificates.
- Added bijections from Fin18 to actual edge subtypes and graph isomorphisms to intrinsic Mathlib line graphs. Charpoly invariance under reindexing removes the last line-index semantics issue.
- Constructed the actual canonical presented RACG and proved forbidden commuting-pair shortening. Initial generic symmetry proof needed Matrix.IsSymm as equality, and simplification had to avoid rewriting canonical-system generators away before applying cancellation lemmas. Corrected build passes strict checking.
- Defined actual length-k shortest-word sets and cardinal counts. Did not equate those definitions with automaton counts.
- Inspected pinned Coxeter.Basic and all Coxeter.Length, plus bounded GroupTheory text/file searches. Matsumoto is explicitly TODO; no available graph-product normal form found. Full converse requires substantial new normal-form formalization, as detailed in FORMAL-GAPS.md. No theorem was replaced by an axiom/hypothesis.

Resource discipline: builds use at most2 Lean worker threads per invocation, bounded3500MB Lean memory and180s timeout. The short tree check briefly overlapped the spectral check; subsequent replay is one combined invocation. No full mathlib rebuild. The combined standalone partial packet uses read-only pinned dependencies. The packet/replay is not an accepted MathDB solution.
