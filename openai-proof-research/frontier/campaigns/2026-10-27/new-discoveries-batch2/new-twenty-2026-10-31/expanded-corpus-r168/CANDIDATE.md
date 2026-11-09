# MathDB 381751 — two diamond-pair components

Verdict: a proved finite refutation candidate, pending independent review and root adjudication. Zero accepted credit is claimed. The target is Conjecture 3 of Anastos–Fabian–Müyesser–Szabó, *Electronic Journal of Combinatorics* 30(3) (2023), P3.10, pp. 2–3; equivalently Conjecture 1.3 of arXiv:2212.03100v2. The published body explicitly says that a component need only fail to be K4. This is not the separate bipartite conjecture, which this construction does not address.

## Exact graph and proof

On vertices 0,…,7, take the three disjoint perfect matchings

- A = {01, 23, 45, 67};
- B = {12, 03, 56, 47};
- C = {02, 14, 36, 57}.

Take two disjoint copies H and H+8 of their union. This is a simple, properly three-edge-coloured cubic graph on 16 vertices, with two connected components of order 8, neither K4. Set n=8 and prescribe (a1,a2,a3)=(1,3,3), whose sum is n−1.

Here is a complete ordinary impossibility proof. In H, B∪C is the alternating cycle 0,3,6,5,7,4,1,2,0. Its bipartition is {0,1,6,7} and {2,3,4,5}. Every A-edge has both ends in one of these parts. A perfect matching of H has equally many A-edges internal to each part, because both parts have four vertices. Consequently a perfect matching using at most one A-edge uses none. The only perfect matchings of the cycle B∪C are B and C themselves. Both contain four edges of one colour. Therefore a matching subject to the caps A≤1, B≤3, C≤3 cannot be perfect in H and has at most three edges. Every hypothetical (1,3,3) matching in the two-copy graph restricts to those same caps in each component, so would have at most six edges. It requires seven, a contradiction.

This is independent of any false motivating theorem. It satisfies even the stronger condition that *every* component is not K4. No claim of minimality is made.

## Evidence and formal semantics

`outputs/matchings.json` covers all colour-preserving isomorphism classes through 12 vertices by fixing A and using alternating-cycle partitions for A∪B, then enumerating every allowable C. `outputs/matchdeep.json` extends the complete coverage to 14 vertices and records the witness encountered during a partial 16-vertex sweep. The searches retain duplicated isomorphism representatives, which does not weaken coverage. Random larger trials are only diagnostics.

`scripts/witness.py` independently checks all 8×56×56=25,088 selections with counts (1,3,3), without the discovery dynamic program. It also enumerates all 4,096 local edge subsets, recording the entire local matching spectrum in `outputs/witness-independent.json`.

`lean/SplitMatching.lean` defines the literal endpoint maps on E=Fin 2×Fin 12 and V=Fin 2×Fin 8. `global_simple` proves no loops or parallel unordered edges, `global_perfect` proves the exact three-colour perfect-matching decomposition, and `graph_edge_iff` identifies these identifiers with every edge of the actual `SimpleGraph`. Thus arbitrary Boolean selection functions parameterize all arbitrary edge subsets. Matching is defined by the usual incidence degree at most one, not by a preselected list of possible matchings. `degree_card`, `lc_card`, and `count_card` certify the cardinality interpretations. `component_at_least_five` proves that an actual reachable component contains five distinct vertices, enough to exclude K4. `literal_counterexample` states the 16-vertex witness and the impossibility using literal filtered edge cardinalities. It has no bounded search predicate as its conclusion.

The local impossibility uses a general twelve-variable natural-number arithmetic lemma, derived by `omega` from the eight vertex incidence inequalities and the three colour caps. All parts are kernel checked. `replay/` is a fresh copied rebuild. `replay/Audit.lean` audits all module-origin declarations, including generated ones, rather than only the final theorem. The audit found 69 declarations, all safe, nonpartial, without added axioms; their transitive axioms are subsets of propext, Classical.choice, Quot.sound. Upstream caches were reused, not rebuilt.

## Novelty and credit risks

The current Lean Pool HEAD, its actual `LeanPool/projects.yml`, all candidate files, eight spaced GitHub repository searches, and complete current scoped Omega D5/Problems and OpenAI preprints trees were screened. No matching prior solution was located. The near Omega hit `PerfectMatchings/InvolutionOrbitSplit.lean` was read and concerns two involutions; it is not the three-colour assertion. See `outputs/registry-screen.json` for exact hashes, queries and limitations. Repository/path screening is not universal code or literature clearance.

The exact current published conjecture and its K4 obstruction were read. The new component is obtained from two K4-minus-edge diamonds connected by two edges; the argument extends the source's parity obstruction. This creates a **material, potentially high substantive-credit risk** under the campaign's prohibition on source-ingredient bridges or short observations. The source does not print this component or this colour-cap obstruction, and the target's explicit non-K4 exception claim is genuinely false; nevertheless root must decide whether the novelty is significant enough. Do not self-accept it.

The author David Fabian's thesis was a relevant prior-art lead. Its institutional URL returned a “Making sure you're not a bot!” page with HTTP 200, retained as such, and was not retried. That thesis body was not read. No global priority assertion is made. This gap and the bridge objection should be resolved in independent review before acceptance. No authors were contacted and nothing was published.
