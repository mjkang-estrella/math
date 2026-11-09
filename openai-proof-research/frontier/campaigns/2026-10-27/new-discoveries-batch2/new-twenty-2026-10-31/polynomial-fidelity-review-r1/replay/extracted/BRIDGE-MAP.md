# Ordinary proof to checked declarations

The ten inherited mathematical source modules are preserved byte-for-byte, including Source.lean. Audit alone is extended. Every declaration below is in namespace PolynomialConvexity.

| Bridge | Declarations / module |
|---|---|
| Concrete exponential model, tails, all power integrability | Inherited Model, Tails, Moments, Integrability |
| Actual mixed layer cake | inherited mixed_layercake / Layercake |
| Actual gap-integral evaluation | inherited gap_integrable, prefix_gap_integral / Factored |
| Null coordinate ties, all labels distinct a.e. | volume_coordinate_ne, volume_coordinates_injective / Ties |
| Measurable strict descending chambers, disjoint and covering a.e. | chamber_measurable, chamber_unique, chamber_cover, chambers_disjoint, chambers_cover_ae / Chambers |
| Actual lintegral partition over all d! permutations | chamber_lintegral_partition / Chambers |
| Concrete tail sum, first containing edge and prefix orientation | vertexThreshold_tailSum, prefix_exponent / Gaps |
| Reindex even when edges repeat | vertexThreshold_relabel, labelled_prefix_exponent / Gaps |
| Triangular gap matrix determinant 1 | gapMatrix_det, gapLinear_det / GapTransport |
| Actual linear equivalence and volume transport | gapEquiv, gap_measurePreserving / GapTransport |
| Adjacent-difference inverse, positive orthant to exact chamber | gapAt_tailSum, gapAt_inverse, gap_positive_iff / GapDomain |
| Labelled measurable equivalence and domain transport | labelledGap_measurePreserving, labelledGap_preimage_chamber / GapDomain |
| Actual chamber integral equals tuple coefficient | chamber_integral / Identification |
| Positive-orthant integral and actual mixed moment | threshold_integral, mixed_moment / Identification |
| Actual factorial identity, every real weight | moment_identity / Endpoint |
| Literal polynomial convexity, simplex, full endpoint | sourcePolynomial_convex_orthant, source_conjecture / Endpoint |

No stabilizer quotient appears. Chamber labels always range over Equiv.Perm (Fin d), independently of the tuple values. An absent vertex contributes zero; a vertex first occurring at k contributes exactly gaps j≥k, giving inclusive prefix cardinalities. The matrix, determinant, measurable equivalence, measure pushforward and domain identity are proved separately rather than hidden in an assumption. Real/ENNReal passage uses checked integrability and nonnegativity.
