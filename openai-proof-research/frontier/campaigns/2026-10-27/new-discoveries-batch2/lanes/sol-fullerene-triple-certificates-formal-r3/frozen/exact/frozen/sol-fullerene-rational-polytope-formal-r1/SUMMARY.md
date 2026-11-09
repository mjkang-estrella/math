# Staged real geometry — incomplete source-class certificate

30 October 2026. Solo implementation. **NO SourceClaim; geometric completion and novelty HOLD. No acceptance or credit. Counts remain 9 additional / 39 total / next40.**

`Literal.lean` defines E=Fin3→ℝ, the ordinary dot product, the one-sided intersection `poly q={x | ∀i, dot(q i)x≤1}`, and its actual supporting sections. It proves closedness, convexity and 0∈interior, so these are genuine full-dimensional real convex sets. `compact_of_positive_span` proves compactness from explicit nonnegative representations of all six signed coordinate functionals. It does not confuse absolute polarity with these one-sided inequalities.

The main geometric progress is `active_kernel_trivial` and `extreme_iff_active_kernel`: a feasible point is an actual mathlib extreme point iff every direction annihilating its active normals is zero. Necessity uses a finite open neighborhood of slack inequalities and a two-sided feasible perturbation, not a combinatorial vertex definition. `extreme_of_active_unique` proves extremality from three uniquely determining active equations. `facetSection_extreme` proves each actual equality section is an extreme face, without asserting its dimension or that every facet occurs.

`InstanceG.lean` and `InstanceH.lean` encode all 32 actual rational normals and all 60 saved rational points as real coordinate functions. Their compactness certificates are positive combinations of the original normals giving each signed coordinate. The generator computes rational inverse coefficients from normals 0,1,2 and adds a common nonnegative shift to all32 coefficients using the zero normal sum. The generated Lean identities independently verify the result algebraically; Python assertions are not axioms. The pG/pH point data are definitions, not yet theorems of vertex completeness.

Exact residual interfaces, in priority order:

1. Extract three independent active normals from the proved trivial active kernel in dimension3. The elementary finite-dimensional rank lemma is **not yet formalized**.
2. Kernel-check the complete feasible triple enumeration and identify its image with the 60 saved points; combine with (1) and `extreme_of_active_unique` to prove `(poly qG).extremePoints ℝ = Set.range pG` and the H analogue. **Neither complete vertex-list equality is claimed.**
3. Prove P is the convex hull of that complete list, and each section the convex hull of its incident sublist. The bounded endpoint/rank-increase argument is described in the frozen audit but not imported as a theorem.
4. Prove the 32 sections have affine dimension2 and exhaust supporting facets; prove each 5/6-cycle gives the entire section's edges, and all primal edges arise this way. Derive cubic vertex incidence and actual facet adjacency equal to each original graph. Degree/count data alone are insufficient.

Thus this packet does not instantiate a literal fullerene or establish the geometric part of the original full source predicate. It is a sound staged geometry component, not a replacement weakened predicate. No analytic/matrix-exponential development, manuscript, or claim about the default source parameters is included.

`coordinate-check.json` records an additional guarded exact-arithmetic evidence check: each graph has 4960 nonsingular triples, exactly60 feasible intersections matching the saved points; 32 noncollinear incident lists (12 of length5,20 of length6); 90 pair-incidence edges matching the frozen original graph, and 90 combinatorial primal edges with cubic incidence and connected facet cycles. These computations are explicitly outside the Lean theorem boundary.

See `PROOF-SOURCES.md`, `RUN.md`, `FAILURES.md`, source bindings, declaration inventory, extracted replay receipt, deterministic source archive and final manifest/verification receipt. Compiler success alone is insufficient: fresh replay additionally rejects diagnostics/panics, disallowed axioms and unsafe transitive declarations, including private/generated owned declarations.

Final extracted replay PASS: all three mathematical modules, Inventory and Audit compiled serially in 45.7 seconds total. All774 owned declarations have individual axiom reports and safety records; the transitive type/body traversal checked2570 declarations. Observed axioms are exactly propext, Classical.choice, Quot.sound. Both literal compactness/interior instances passed; no diagnostic/PANIC appears in the extracted replay. All owned compiled artifacts were removed after replay. `audit.json` independently reconciles the complete inventory against all axiom reports.
