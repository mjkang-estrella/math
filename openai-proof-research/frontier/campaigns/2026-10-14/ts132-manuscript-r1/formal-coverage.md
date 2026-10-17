# Scoped formal support mapped to the manuscript

The implementation is ts132-formal-v1, namespace TSLocal. This manuscript author read the complete 311-line TSLocal.lean and the initial 79-line Controls.lean. TSLocal remained identical at final sealing; after Controls changed, the complete final 87-line file was reread. Final identities were authenticated against the externally received seal. Its independent implementer read the entire formal-support.tex and confirmed its coverage/exclusions match the compiled module. That coordination is not an independent formal verdict. Exact final manifest/source/coverage anchors are in inputs/dependencies.json and formal-dependency.json.

Compiler contract: Lean4.34.1; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. The implementation reports22 support theorems /29 public declarations and13 control theorems /14 control declarations, using standard transitive axioms. The manuscript makes no whole-theorem formalization claim. Read the sealed implementation's coverage, type/axiom output and validation receipts for exact signatures and trust assumptions.

| Declarations | Actual mathematical interface / manuscript connection |
|---|---|
| tournament_card_le_three | Finite set, irreflexive total directed relation and at-most-one predecessor at each vertex imply cardinal≤3. Empty/singleton cases included. This is a general relation statement; no finite field or Paley predicate is constructed. |
| fiber_card_bound | Explicit finite image-cardinality and per-fiber-cardinality hypotheses imply a product bound. |
| Word, edgeLabel, HeadConstant; head_fiber_constant, head_image_indegree, head_constant_card, head_constant_four | Actual nested-product words and Option-valued first-difference labels; head labels inherited in a fiber; quotient predecessor uniqueness follows from difference cancellation; the induction proves≤3^h and<82 at h4. Additive-group and assumed irreflexive total base relation hypotheses remain visible. |
| affineVector; affine_difference, affine_coordinate_eq_iff, affine_first_difference | Scalar affine difference formula and preservation of given coordinate equality/inequality, including explicit hypotheses that earlier coordinates agree and the specified coordinate differs. |
| rowPositionMap; rowPosition_injective, rowPosition_transitive, rowPosition_comp, rowPosition_one, rowPosition_left_inverse | Field K, function vectors ι→K and subgroup H≤Kˣ; exact affine maps and label multiplication; injectivity, moves between arbitrary pairs, composition, identity and left inverse. These operate in a separate function-vector representation, not a proved equivalence with Word. |
| profileEnvelope; envelope_le_two, coupled_profiles | Real L,ε≥0; finite d; ε·3^(d+1)≤2; initial u0≤L,v0≤0 and the two scalar recurrences for n<d. For n≤d, explicit envelope, v_n≤εL(3^n−1) and u_n≤2L. |
| normalize_one_side | Assumes M>0,A≤M²,r/M≤ε,u,v≥0 and already-derived scalar s,j inequalities; concludes the one-side normalized bounds. |
| normalized_zero_side | Assumes t/M≤ε,u≥0 and already-derived scalar s,j inequalities; concludes zero-side normalized bounds. |
| strict_seed_numbers, strict_seed_ratio, strict_seed_from_ratio, strict_seed_parameters | Exact integer/rational depth20 gain; ratio implication under A>0; strict (44M^21)²<M²k^20 under M>0,3M²≤2k. |

Not formalized: finite-field square/non-square orientation at primes3mod4; regular outdegree and alphabet cardinal for the actual Paley relation; Word/function-vector representation identification and the complete Paley gate-label covariance; nested Boolean functions and common all-index raw-bit action; sensitivity/joint-profile definitions and all four combinatorial recurrences; prime existence, integer rounding and actual parameter selection; disjoint zero blocks; OR balancing and Boolean composition; logarithmic alpha and either full theorem endpoint.

The manuscript reproduces those mathematical arguments in prose. It does not replace them with conditional Lean conclusions, finite tests or an axiom named after the theorem. No external proof package is silently imported into the claimed local support.
