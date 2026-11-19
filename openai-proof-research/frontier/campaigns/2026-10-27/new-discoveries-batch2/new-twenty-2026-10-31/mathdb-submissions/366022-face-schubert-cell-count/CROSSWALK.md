# Source appendix crosswalk

Appendix SHA-256 \`22166f4ad321c87f5cd23e86b910e55dbf7ea53551bf56bff23c20e452e54775\`. Block offsets in the JSON map are zero-based bytes. Lines are one-based.
Every row links to the exact extracted module. Source, author and local olean identities and individual receipt hashes are in the machine-readable maps.

| Block | First appendix source line | Compile / check | Paper claim | Checked anchors |
|---|---:|---|---|---|
| [PinsProbe](src/PinsProbe.lean) | 8 | F01-PinsProbe / F02-PinsProbe | §6 — Runtime pin and narrow import set | [replayed stdout](F01-PinsProbe.output.txt) |
| [Geometry](src/Geometry.lean) | 32 | F03-Geometry / F04-Geometry | §2 — Rational generators, real convex hull and supporting faces | \`gQ\` (L8), \`P\` (L27), \`face_hull\` (L52) |
| [Edges](src/Edges.lean) | 135 | F05-Edges / F06-Edges | §2 — Four controlling edges and classification in the planar quartet | \`edge12\` (L76), \`edge14\` (L84), \`edge23\` (L92), \`edge34\` (L100), \`planar_edges_iff\` (L214) |
| [Interior](src/Interior.lean) | 369 | F07-Interior / F08-Interior | §3 — Explicit graph-plane witnesses and a common intrinsic interior region | \`Graph\` (L8), \`witness_graph\` (L78), \`witness_interior\` (L134) |
| [Chow](src/Chow.lean) | 515 | F09-Chow / F10-Chow | §4 — Stacked determinants and strict product over all actual edges | \`chow_quotient\` (L36), \`chow12\` (L48), \`chow14\` (L53), \`chow23\` (L58), \`chow34\` (L63), \`all_edge_product_pos\` (L115) |
| [NativeEdges](src/NativeEdges.lean) | 659 | F11-NativeEdges / F12-NativeEdges | §2 — Exposed dimension-one faces and nondegenerate segments | \`ExposedEdgeFace\` (L8), \`dim_one_face_iff\` (L91) |
| [Interface](src/Interface.lean) | 772 | F13-Interface / F14-Interface | §§3–4 — Shared interior and all-edge certificate | \`certificate\` (L120) |
| [Incidence](src/Incidence.lean) | 906 | F15-Incidence / F16-Incidence | §§1, 4–5 — Plane/edge incidence and necessity of the first-minor chart | \`det_ne_zero_iff_disjoint\` (L65), \`p12_ne_zero_of_away\` (L106), \`graph_witness_stab_complement\` (L113) |
| [Normalized](src/Normalized.lean) | 1037 | F17-Normalized / F18-Normalized | §§1, 5 — Normalized basis, determinant scaling and graph uniqueness | \`normalized_span\` (L44), \`normalized_chow\` (L74), \`graph_coords_unique\` (L92) |
| [Chart](src/Chart.lean) | 1143 | F19-Chart / F20-Chart | §§1–2, 5 — Full graph equivalence and actual face-span family | \`complementChart\` (L53), \`native_edge_span_iff\` (L61), \`away_native_iff\` (L71) |
| [Cone](src/Cone.lean) | 1243 | F21-Cone / F22-Cone | §§2–3 — Real convex combinations and exact nonzero-cone stabbing | \`mem_P_iff\` (L12), \`InPositiveCone\` (L32), \`stabs_iff_nonzero_cone\` (L66) |
| [Signs](src/Signs.lean) | 1325 | F23-Signs / F24-Signs | §§4–5 — Every ordered authentic edge and the nonzero b separator | \`EdgeIndex\` (L6), \`witness_sign_equal\` (L53), \`same_sign_b_ne_zero\` (L64) |
| [ChartTopology](src/ChartTopology.lean) | 1416 | F25-ChartTopology / F26-ChartTopology | §5 — Connectedness and separation in graph coordinates | \`preconnected_chart_sign_const\` (L34), \`no_preconnected_chart_witnesses\` (L41) |
| [Plucker](src/Plucker.lean) | 1476 | F27-Plucker / F28-Plucker | §1 — All six minors, common scalar under basis change and span recovery | \`minors\` (L9), \`minors_ne_zero\` (L56), \`spanPair_eq_of_minor_scale\` (L64), \`minors_scale_of_spanPair_eq\` (L111) |
| [Projective](src/Projective.lean) | 1609 | F29-Projective / F30-Projective | §1 — Quotient topology, decomposable image and actual Grassmannian embedding | \`project_quotient\` (L31), \`plucker_injective\` (L62), \`plucker_range\` (L97), \`realGrTopology\` (L106), \`plucker_embedding\` (L109) |
| [ProjectiveChart](src/ProjectiveChart.lean) | 1727 | F31-ProjectiveChart / F32-ProjectiveChart | §1 — Open projective patch and normalization by its first coordinate | \`firstPatch_open\` (L14), \`projectRatios_continuous\` (L31), \`firstPatchHomeomorph\` (L54) |
| [NativeChart](src/NativeChart.lean) | 1810 | F33-NativeChart / F34-NativeChart | §§1, 5 — Homeomorphism on the entire native stabbing complement | \`NativeStabs\` (L6), \`NativeAway\` (L9), \`nativeChartHomeomorph\` (L100), \`nativeChart_agrees\` (L105) |
| [NativeChow](src/NativeChow.lean) | 1925 | F35-NativeChow / F36-NativeChow | §§1–2, 4 — Signed complementary minors and fixed edge choices | \`primalMinors\` (L8), \`sourceChow_det\` (L15), \`NativeEdgeSpan\` (L37), \`edgeSpanOfIndex_surjective\` (L43), \`indexedChow_scale_of_same_span\` (L60) |
| [NativeSigns](src/NativeSigns.lean) | 2008 | F37-NativeSigns / F38-NativeSigns | §§1, 4–5 — Global reversal quotient and edge-sign equality on the chart | \`ProjectiveSigns\` (L55), \`nativeSign_of_basis\` (L96), \`chartSpanBits_no_flip\` (L163), \`nativeSign_on_chart_eq_iff\` (L178) |
| [NativeCount](src/NativeCount.lean) | 2198 | F39-NativeCount / F40-NativeCount | §§5–6 — Actual components, sign surjection, repeated fiber and count scope | \`componentSign_surjective\` (L64), \`componentSign_not_injective\` (L68), \`native_finite_cell_count_gt\` (L75), \`native_nat_cell_count_ne\` (L83) |
| [NativePolytope](src/NativePolytope.lean) | 2303 | F41-NativePolytope / F42-NativePolytope | §§2–3 — Actual projective cone image, rank-three affine hull and height patch | \`affineHull_dim\` (L37), \`heightHomeomorph\` (L129), \`projectivePolytope_image\` (L166), \`native_witness_interior\` (L182) |
| [LiteralEndpoint](src/LiteralEndpoint.lean) | 2499 | F43-LiteralEndpoint / F44-LiteralEndpoint | §§1, 5–6 — Literal projective domain and non-bijection/count endpoints | \`pluckerHomeomorph\` (L6), \`literal_complement_eq\` (L50), \`literal_no_bijection\` (L76), \`literal_cell_count_ne\` (L70), \`mathdb_366022_counterexample\` (L83) |
| [NativeAudit](src/NativeAudit.lean) | 2596 | F45-NativeAudit / F46-NativeAudit | §6 — Independent replay of the author endpoint signature and axiom commands | [replayed stdout](F45-NativeAudit.output.txt) |

The separately authored [IndependentAudit](src/IndependentAudit.lean) is supplemental. F48 and F49 check the expanded domain and sign range, the literal endpoints, and recoverability of each edge from its span. It is outside the canonical appendix. See the [signature map](SIGNATURE-MAP.json) and [axiom map](AXIOM-MAP.json).

[Paper](PAPER.md) · [Exact appendix](LEAN-SOURCE-APPENDIX.md) · [JSON crosswalk](CROSSWALK.json)
