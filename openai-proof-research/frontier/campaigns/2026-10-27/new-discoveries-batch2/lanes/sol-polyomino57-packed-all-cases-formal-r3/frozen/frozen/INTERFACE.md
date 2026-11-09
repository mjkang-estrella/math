# Closed interfaces (partial task result)

All names below are under `Polyomino57.Diagonal.FiniteProof`, except benchmark names and frozen names.

* `liftPotential`, `lift_at`, `lift_certificate`: lift an actual indexed GraphPotential.Certificate along an injective Cartesian point map to its finite image. No connectivity transport premise and no soundness reproof.
* `excludes`: given indexed certificate, literal `domain = image`, original-group membership for each label, label nonemptiness, and full potential ≥12, proves the literal finite-case assertion for original groups. Pruning equivalence is unnecessary in this direction: hitting original groups implies hitting selected original groups.
* `checked_certificate`: finite powerset checks for base, edge, and ALL ordered disjoint nonempty pairs imply the frozen Certificate. No symmetry shortcut, bitmask disjointness assumption, or subtraction.
* `Small.point`, `Small.group`, `Small.mask`, `Small.value`: explicit 60 indexed Cartesian vertices, four retained groups, membership encoding and balanced lookup of all 960 supplied bytes for (10,10,1).
* `Small.domain_eq`, `point_injective`, `groups_mem`: ordinary kernel decide proves the actual literal domain identity, injection, original-group membership. Actual adjacency is `Polyomino57.Adj (point i) (point j)` throughout.
* `Small.base_check`, `edge_check`, `merge_check`, `full_check`, `certificate`, `case_10_10_1`: COMPLETE literal nonvacuous boundary-only exceptional case, using the immutable soundness component. Edge check is split into 60 row theorems. Original group memberships can overlap; base checks all subset masks. No rowcount assumption is a hypothesis.
* `case_a_b_e` in Empty00..Empty34: 35 literal original-group cases, each through an explicit canonical collision center and an empty collision group proved by integer arithmetic. No Python-computed truth is assumed.
* `case_7_3_0`: sixteen distinct cells are forced via original singleton collision groups; any hitting Q contains all sixteen, contradicting card 11.
* `completed`: literal finite set of these 37 triples.
* `completed_card : completed.card = 37` and `completed_canonical : completed ⊆ canonicalCases`.
* `completed_cases`: original finite assertion for every c in completed.
* `RemainingCases`: literal original assertion for each c in canonicalCases with c ∉ completed.
* `remaining_card : (canonicalCases \\ completed).card = 33`.
* `finiteCases_iff_remaining : FiniteCases ↔ RemainingCases`.
* `universalContainer_of_remaining (h : RemainingCases) : UniversalContainer 11 witness` (CONDITIONAL, explicit sole remaining premise).

The 33 remaining cases are the other 30 potential tables and three forced-cell cases (7,4,0), (8,3,0), (8,4,0). No theorem asserting RemainingCases or FiniteCases is supplied. The original final placement is translation-only through the unchanged canonical recovery theorem, and the container definition retains witness_connected.

`LargeBenchmark.checked` in Large16 verifies exactly 384 sampled original largest-table merge inequalities (full mask 16383, proper left masks 1..16, all 24 roots). This is a measured benchmark, NOT another finite case or Certificate.
