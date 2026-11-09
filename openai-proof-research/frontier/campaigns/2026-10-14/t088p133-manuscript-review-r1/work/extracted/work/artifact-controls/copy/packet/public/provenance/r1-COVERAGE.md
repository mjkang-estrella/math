# Coverage and limits

The complete mathematical draft retains the exact frozen theorem, including every nonsimple, repeated-Gale, zero and boundary case. It neither weakens to generic polytopes nor extends to >=7 facets or dimensions 5-8.

| Obligation | Manuscript coverage |
|---|---|
| Facet positivity, distinct actual normals, spanning and balance | Section 2; divergence and compactness; Section 4 nonzero-middle exclusion |
| Projection/zonotope factors | Section 2, Cauchy endpoint counting and extrusion induction |
| Mixed-volume hypotheses, trial negative supports | Section 2; precise inequality and first variation; exact section maximum |
| Attainment, interior maximizing level | Exact maximum lemma and Proposition A; no boundary-vanishing assumption |
| Complementary determinants, Euclidean simplex volume, coarea, Gamma/factorials | Section 3, every normalization explicitly derived |
| Centering, scaling, asymmetric Laplace signs | Section 4; coefficients centered once; density evaluated at minus W |
| Log-concavity, conditioning, survival integration and boundary terms | Section 5; usable Prekopa hypotheses and direct HNBUE-Laplace derivation |
| Universal two-bracket algebra, positivity and one-sided cases | Proposition B; direct cleared expansion, Cauchy-Schwarz and strictness |
| Partial fractions, alternating signs and exact quotient identity | Section 7; signed bilateral transforms and polynomial divisibility |
| Exact ten-pattern positivity and repeated-rate strictness | Section 7 and Appendix A, full 248-term sparse certificate and pure positive endpoint terms |
| Zeros and all-zero vector | Explicit reclassification and direct zero case; no density claim at b=0 |
| Minimum facet classification, affine invariance, simplex value | Section 8; polar classification, transformed area vectors and exact determinants |
| Method limits | Section 9; exact corner calculation, no geometric conclusion beyond scope |
| Attribution and PQ1-PQ5 | Section 1 and Appendix B; adopted joint-assembly assessment and bounded search/read limits |

Formal support is **pending**. No independent formal verdict is available to this draft. The separately assigned deterministic Proposition B rational-mixture/two-bracket task uses Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, according to the user's brief only. That task and its active root were not inspected, imported or polled. No declaration names, compiled artifacts, formal PASS or realized formal coverage are claimed.

The full theorem, geometry, probability, coefficient certificate and assembly are not formalized here. The new symbolic Python identity check is exact finite algebra, not Lean support or an independent verdict. Formal integration and its independent review belong to a later immutable draft round. No acceptance, count change or release claim follows from this implementation.
