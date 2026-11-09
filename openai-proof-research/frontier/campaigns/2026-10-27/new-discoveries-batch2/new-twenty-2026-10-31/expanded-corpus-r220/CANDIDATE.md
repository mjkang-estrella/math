# Candidate status

**No qualifying candidate. Credit requested: zero.**

No literal Lean endpoint is justified by the evidence in this lane. The exact searches found no counterexample, and the proof attempts leave universal lemmas open. Numerical agreement is not promoted to a proof or a surrogate Lean predicate.

The strongest remaining routes, ranked by likely certificate cost, are:

1. **366794:** a literal king-game counterexample would have a short mex-table certificate, but none occurred for odd r through 33 and k through 300. A full proof requires a boundary-state invariant uniform in r and k. The source's rectangle and r=1 staircase lemmas do not immediately supply it.
2. **366989:** an explicit subset with more bases would permit a finite rank certificate. Exact rank-4 and selected rank-5 exhaustive searches, rank-5 random search, and rank-6 local search found none. The source already knows c=1. A full proof for c>=2 needs a new inequality on subspace intersections.
3. **367191:** an explicit strongly connected digraph with subset-pair obstruction is finitely checkable. All digraphs through five vertices passed. Extending the singleton proof by contraction has an unproved component-preservation bridge.
4. **366899:** a graph without a terminal set would require certified exhaustive general-position and endpoint checks. Sampled graphs beyond the published order-11 range all had terminal sets. This route has higher search and certificate cost.

For basis diagnostics, the rank-r count was computed using the subspace-lattice identity

`r! b(S) = sum_(W <= F_2^r) (-1)^(r-dim W) 2^binom(r-dim W,2) |S intersect W|^r`.

Indeed the sum counts ordered r-tuples spanning the ambient vector space by Möbius inversion. A spanning r-tuple is independent and has r distinct nonzero entries, so each basis has exactly r! orders. Rank-4 enumeration instead counted independent subsets directly and applied the subset zeta transform. These algorithms are ordinary exact diagnostics; no checker soundness theorem was formalized.

Before any renewed candidate claim, finish its exact current public-proof registry audit, citation-neighborhood/body checks, and comparison against all printed examples across versions. No worldwide novelty, independent review, root acceptance, or campaign increment is asserted here. The unimplemented per-target searches and unread bodies are explicit in `results.json` and `SUMMARY.md`.
