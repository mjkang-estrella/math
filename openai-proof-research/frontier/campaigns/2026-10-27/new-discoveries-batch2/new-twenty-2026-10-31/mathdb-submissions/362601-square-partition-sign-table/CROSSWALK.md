# MathDB 362601 source and declaration crosswalk

The retained [MathDB projection](inputs/362601-MATHDB-PROJECTION.json) identifies Roy's square-power partition conjecture and prints its equality lists. Roy v4, §3.1, defines the square-power count by restricting each part to a perfect square. Conjecture 3.2 and the [rendered Table 2](sources/roy-v4-p10-crop.png) give the entire oriented sign classification. The [retained v4 text](sources/roy-v4.txt) and [PDF response receipt](sources/roy-v4-pdf-response.json) bind the source wording and version. The PDF body SHA-256 is 9ba42d349c6273ffd64060f00bacc5ac7f0d23ee1e63a8b7213e1f2c7ec38882.

## Native row reconciliation

Every row is interpreted with \(1\le m\le n\). Entries in the failure test below are shown as encoded, including the inert exclusions in the native print.

| \(m\) | EqRow membership and MathDB list | FailRow test and Roy failure cell | Scope check |
|---|---|---|---|
| 1 | 1, 2, 4, 5, 6, 9, 10, 13, 14, 18, 22 | Outside that list | Complement on \(n\ge1\) |
| 2 | 4, 5, 9, 13 | Outside 1, 4, 5, 9, 13 | Exclusion 1 inert on \(n\ge2\) |
| 3 | 4 | Outside 1, 2, 4 | Exclusions 1 and 2 inert on \(n\ge3\) |
| 4 | 5, 6, 7 | False | Blank failure cell |
| 5 | 5, 6, 8, 11, 15 | Membership in 7 | Listed failure |
| 6 | 8, 10, 12, 14 | Membership in 6, 7, 11, 15 | Listed failures |
| 7 | 8, 9, 12, 13, 19 | Membership in 7, 10, 11, 14, 15 | Listed failures |
| \(\ge8\) | Empty list | False | Strict positivity throughout |

The rendered table, projection equality lists, and literal constructors agree row by row. The [row comparison record](NATIVE-ROWS.json) gives the sets and inert entries. The complement of both predicates is precisely the strictly greater case, by the third component of Signs. Positive unordered inputs are interpreted by sorting the two arms.

## Declaration and dependency map

| Mathematical obligation | Checked declarations |
|---|---|
| Literal underlying partition type | Pinned Mathlib's Nat.Partition has parts : Multiset ℕ, a positivity field and exact sum field. Its Fintype counts each partition once. Nat.Partition.restricted filters the universal finset on a part predicate. |
| Square restriction and unrestricted multiplicity | [Base](src/Base.lean) Sq, Big, Squares, P. Sq uses a positive natural root, with no cardinality, distinctness or multiplicity bound. A partition of zero has empty parts by positivity and the sum field. |
| Count bridge and increments | [Base](src/Base.lean) strip, pad, both inverses, padding, card_F, P_mono and P_succ_lt_iff. [Increment](src/Increment.lean) P_restricted identifies the whole subtype with the actual finset by membership equivalence. removeOne, noOnes and P_add_exact split on the presence of a one. |
| Sorted cutoff | [Cut](src/Cut.lean) list_cut, earlier_suffix, exists_crossing, Crossing, root_spec, root_min, Crossing.offset and root_two. The cut uses weak inequalities across equal parts. [Certificates](src/Certificates.lean) crossing_slack exposes the strict crossing and available weight. |
| Small-multiset facts | [Code](src/Code.lean) eq_zero_of_sum_lt_four, eq_one_four_of_small and y₀_cross. |
| Ordinary coding | [OrdinaryCode](src/OrdinaryCode.lean) ordinary_cover, ordinaryDecode, OrdinaryFormat, dropFour_add, minPart_add and erase_one_add. These allow extra fours in the data exactly when the data square is 4. |
| Seven exceptional transports and bulk omission | [Bulk](src/Bulk.lean) bulk_exceptional, prevDecode, bulkDecode, bulk_on_ordinary, bulkUnused, bulk_cover and bulkEncode_spec. The unused pair contains two fours in each coordinate. bulk_strict applies cross_card. |
| Thin code and spare slot | [Thin](src/Thin.lean) slot_sum, slot_sep, slot_ne_y₀, slot_impossible, thinDecode, thin_cover, thinUnused and thinEncode_spec. The slack-49 interval supplies the unused first coordinate. thin_strict applies cross_card. |
| Actual recurrence and bounded arithmetic | [Recurrence](src/Recurrence.lean) allowed_no, allowed_yes, allowed_step, coeff_spec, parts58_complete, P_coeff, coeffFuel_spec and P_C. [FiniteSigns](src/FiniteSigns.lean) finite_certificate proves the Fin 24 × Fin 52 implication filtered by FiniteRegion using decide, and finite_signs transfers it to P. [Certificates](src/Certificates.lean) coefficient_list checks all 59 values. |
| Small positive arms and gap support | [Small](src/Small.lean) gap_certificate, succ_gap, represent_ge24, represent_iff_not_gap, P_eq_window, small_P_one, small_tail, and small_window_table. The assembled theorem uses finite_signs for \(n<23\) and small_tail for \(n\ge23\). |
| All signs and sorted arms | [FiniteSigns](src/FiniteSigns.lean) equalValues, EqRow, FailRow and Signs. [Table](src/Table.lean) sign_table_ordered makes the exhaustive range split. sign_table sorts by min and max using le_total. ordered_eq, ordered_lt, ordered_gt and square_partition_eq/lt/gt expose the six iff statements. |
| Literal endpoint | [Certificates](src/Certificates.lean) restricted_sign_table rewrites via P_restricted at both arms and their sum and applies sign_table. Its only inputs are two natural arms, positivity of each, and a decision instance for Sq. |
| Kernel and trust | [Audit](src/Audit.lean) supplies the 57 baseline roots and printed signatures. [ReviewerAudit](src/ReviewerAudit.lean) separately checks a bounded decision procedure for square membership and the visible local declaration closure after the baseline. |

The dependency signatures are in [SIGNATURES.txt](SIGNATURES.txt). The [axiom evidence](AXIOMS.txt) is the extracted axiom portion of the exact [audit stdout](AUDIT-STDOUT.txt). [PAPER.md](PAPER.md) gives the complete ordinary proof and the hand finite certificate.
