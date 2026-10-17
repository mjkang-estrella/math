# Exact scope of the separate Lean support

External package: ../complex-projector-borsuk-formal-v1. No files there were edited.
Manifest output-manifest.json SHA256 28429901ed26db71aaa1bc3b4b7c62c1f2c38f945510e04ba4e4f48eb5893700.
BorsukLocal.lean SHA256 8c6863344596404bf7f8e13e341972510f3ad7d4fa63308a9d31872a9d947cab.
coverage.json SHA256 705df89da3ec6ef20eb0013d3c24a2839b6f340357d52bb23bc30a79470871d9.

Read complete coverage.json, README.txt, public types/axioms output and verifier. Ran its inspected read-only verifier with the external manifest anchor and --check-inputs: 57 payloads authenticated, external inputs unchanged; full_B8C_formalized=false, count_change=0. No formal rebuild was run here. The worker retains two fresh builds, 16 support theorems, 13 controls, and five rejected false variants. These are verification receipts, not an independent formal audit verdict.

Pinned environment recorded by the formal package: Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Its public types use only propext, Classical.choice and Quot.sound. No new upstream theorem axiom is asserted.

| Manuscript interface | Lean declarations | Boundary |
|---|---|---|
| Lemma4.2 three scale cases | favored_case, transverse_square, other_large_case, favored_small_case, two_trio_margin | Universal real inequalities; no ray/trio existence |
| Constants (4.2),(4.7) and chart bounds | favored_radical_lower, other_radical_upper, radius_sq, radius_bounds, chart_bounds | Scalar radical/norm-coordinate bounds |
| Given estimates (4.5),(4.6), one score exceeds1/2 | two_trio_scaled_positive, local_score_improves | Existence of actual scores satisfying those hypotheses is not formalized |
| Identity (4.3) | score_numerator_expansion, score_scaled_expansion | Arbitrary complex q,D and real epsilon,b; geometric identification q=gamma z2, b=abs(z3), D=the tangent expression remains human |
| Complement inequality in Theorem5.1 | complementary_margin | Assumes eta>0 and perturbation score bounds; no compactness proof |
| Final score incompatibility | bessel_cap_incompatible | Scalar contradiction only; Bessel's inequality and attainment of diameter remain human |

The full Hermitian extension, arbitrary-cover enlargement, topology, Hesse/MUB identities, equality locus, cyclic assignment, phase choices, Cauchy–Schwarz production of the two estimates, compactness, cell construction and strict attained diameters are not formalized. Section7 of the manuscript states these boundaries. No full B8C Lean theorem is claimed.
