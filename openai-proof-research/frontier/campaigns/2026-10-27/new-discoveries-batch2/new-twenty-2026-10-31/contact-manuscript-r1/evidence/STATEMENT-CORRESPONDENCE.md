# Statement correspondence

All 18 inherited Lean modules and five inherited scripts are byte-identical. The inherited correspondence is retained at `inputs/STATEMENT-CORRESPONDENCE.md`; input hashes are recorded before and after. No inherited definitions, graph, colors, source assertion, polynomials, degree conventions or contact predicates are changed.

| Declaration | Statement or role | Status |
| --- | --- | --- |
| `half_plane_contact_six` | `HasHalfPlaneContact R 6` | Inherited |
| `R_roots_localize` | For every ε > 0, eventually every root of R x tends inside the ε ball about 0, uniformly over roots | Proved from exhaustive analytic branches |
| `half_plane_contact_six_localized` | Strengthens the inherited half-plane branch proof to any prescribed ε > 0, lower constant 1/4 for every root and a witness with upper constant 1 | Proved |
| `numerator_root_iff` | For real x ≠ 0 and 1+v ≠ 0, numerator(-beta x,v)=0 iff R(x,star(betaInv v))=0 | Proved using clearing, real coefficients and `R_from_quotient` |
| `pole_root_maps_to_numerator` | Every pole root u with Im u < 0 maps to beta(star u) | Proved |
| `numerator_images_localize` | For every ε > 0, all images of lower-half-plane roots eventually lie in the disk and within ε of 1 | Proved before using witnesses |
| `beta_height_comparison` | For Im y > 0 and norm y < 1/2, Im y/2 ≤ 1−norm(beta y) ≤ 16 Im y | Proved |
| `circleChart_real` | i(1+z)/(1−z) is real for norm z = 1 | Proved |
| `circleChart_bounds` | Near −1, norm(z+1)/2 ≤ abs x ≤ norm(z+1) | Proved |
| `bidisk_contact_six` | `HasZeroSetContact (eval₂ bidiskNumerator) (-1) 1 6` | Unconditional; ρ = 1/2, c = 1/512, C = 16 |
| `bidisk_not_contact_two` | `¬ HasZeroSetContact (eval₂ bidiskNumerator) (-1) 1 2` | Unconditional |
| `candidateCertificate` | Reduced certificate for actual graph resolvent, numerator bidiskNumerator, denominator bidiskDenominator, bidegree (3,2), phase 1 | Inherited unconditional certificate |
| `nearest_w_one` | Nearest w-colored vertex has distance 1 | Inherited |
| `ContactPilot.refutation` | `¬ ContactPilot.SourceConjecture` | Unconditional, via `refutation_of_bidisk_contact bidisk_contact_six` |

The universal `SourceConjecture` is untouched: all finite colored simple graphs, every root and every reduced certificate, and all positive even contact orders, must satisfy K = 2d. The inherited graph has d = 1; contact six gives 6 ≠ 2. The separate contact-two exclusion also rules out the predicted order directly. This is a formal completion; independent source-fidelity, novelty and acceptance adjudication belong to root.
