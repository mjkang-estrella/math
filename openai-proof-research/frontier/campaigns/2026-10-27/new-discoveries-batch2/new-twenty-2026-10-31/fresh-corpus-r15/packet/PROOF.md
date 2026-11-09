# Candidate 335230: heterogeneous three-color parts violate the proposed minimum

Status: complete ordinary proof and Lean certificate; zero self-awarded credit. Independent fidelity, significance, prior-art, manuscript and root acceptance reviews remain.

Use the actual source definition: a usage vector has nonnegative real entries summing to one. Adjacent vertices contribute the sum, over colors, of the smaller usage. Vertex defect is the sum over neighbors; graph defect is the maximum over vertices. There is no requirement that vertices in one independent part receive the same usage vector.

Take four independent parts A,B,C,D of size two, with all cross-part edges and no within-part edges. Use the following three-color vectors:

|vertex|usage vector|defect|
|---|---|---|
|A0|(0,0,1)|2/3|
|A1|(0,0,1)|2/3|
|B0|(0,2/3,1/3)|5/3|
|B1|(0,2/3,1/3)|5/3|
|C0|(0,1,0)|5/3|
|C1|(1,0,0)|5/3|
|D0|(2/3,1/3,0)|5/3|
|D1|(1,0,0)|1|

Every row is admissible. Summing the three coordinatewise minima against the six neighbors gives the displayed defects. Consequently the source minimum is at most 5/3, strictly less than (ceil(4/3)-1)*2=2. This refutes the universal conjecture in its exact positive-parameter scope; the exact optimal value is not claimed.

The essential feature is that C and D are heterogeneous. Restricting each part to a single replicated vector would force the known complete-graph lower bound and miss this witness. Neither the known two-color theorem nor the divisible-number-of-parts theorem covers this case. The other grid witnesses in fraction.log are the same proposed outcome, never separate credits.

## Lean correspondence

`Vertex m a` is `Fin (m+1) × Fin (a+1)`: source part count and part size are strictly positive. `Adj` means unequal first coordinates, exactly complete multipartite adjacency. `Coloring m a k` assigns a real usage for each of `k+1` colors. `Valid` includes every source simplex constraint. `defect` is Equation (1); summing zero for nonneighbors is exactly summing over the neighborhood. `graphDefect` is the finite maximum of this function, not a proxy statistic. `MinimumDefect` is `IsLeast` of all admissible graph-defect values. Its negation at indices (3,1,2), value 2, is the literal failure of the source minimum claim. This needs no independent proof that another optimum exists: a smaller feasible objective alone disproves the claimed minimum.

`D` is also defined as the infimum of the very same objective values. Nonnegativity supplies boundedness below, the witness supplies nonemptiness, and `D_witness_le` proves the actual infimum bound. `D_eq_of_minimum` proves identification with any source minimum. Both universal formulations are formally negated: `source_conjecture_false` and `numerical_source_conjecture_false`. `D_strict_counterexample` is the strict numerical endpoint. The ceiling of a ratio of positive integers is encoded by the usual exact natural-number formula `(M+K-1)/K`; the relevant evaluation is kernel checked. No floating-point argument, optimizer output, grid exhaustiveness or helper alone is used in the proof.

## Sources and bounded prior-art limits

Primary: https://arxiv.org/pdf/1702.01442v2 (7 November 2019), Section 2 Equation (1), Section 3.3 definition of composition, Proposition 4, Proposition 5, Conjecture 2, and Proposition 6 with Observations 1–3 and Lemmas 5–7. The complete proofs of the relevant general lemmas and Proposition 6 were read, not just the abstract. v1 was also fetched: the same conjecture and two-color result persist. The author-hosted undated manuscript at https://people.computing.clemson.edu/~goddard/papers/fractionalDefectPreprint.pdf labels the target Conjecture 1 and the divisible case Proposition 6; definitions and target are unchanged, but the two-color proof is organized differently. It is not established to be a version of record. Current arXiv metadata on Nov 1 lists v2 as last revised version and supplies no journal reference. A distinct published final body has not been identified or compared.

Xu's 2016 thesis is a relevant predecessor: https://open.clemson.edu/all_dissertations/1650/ . Only its abstract/landing page was read. The linked full-body URL https://open.clemson.edu/cgi/viewcontent.cgi?article=2651&context=all_dissertations returned 403 on Nov 1; not retried or bypassed. Thesis-body subsumption remains a real unresolved review obligation.

Current searches included the exact title, author names with fractional defect, conjecture plus multipartite, and counterexample plus 5/3. Located author manuscript retains the conjecture. Search misses establish no novelty. Current OpenAI/math verified receipts are reused at head 4eaee87548250b2682affda7d05d947c05554bae (Nov1 05:27 UTC), with separate complete preprints subtree observed 05:55. Targeted paths and cached contents are screens, not full-body searches; the root tree is truncated. Inherited Palomar403 and MathDB403 were not retried. No current solution/comment clearance, subscription-index completeness, exhaustive worldwide search, or priority claim is made.

## Replay and trust

Packet pins Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and includes the dependency lake manifest. Run `python replay.py` in a fresh extraction, overriding LEAN_BINARY and MATHLIB_PACKAGES if needed. It uses at most one Lean worker, a 90-second CPU limit, 105-second wall timeout, Lean -M2048 and 8 GiB virtual-address cap. A first extracted run with a 3 GiB address cap could not create a runtime thread; it was corrected, not reported as a pass. This replay trusts the supplied prebuilt mathlib/dependency olean cache; dependencies were not rebuilt from source. All eleven mathematical theorem declarations have transitive `#print axioms` audits; only propext, Classical.choice and Quot.sound occur. No prohibited proof facility is used.
