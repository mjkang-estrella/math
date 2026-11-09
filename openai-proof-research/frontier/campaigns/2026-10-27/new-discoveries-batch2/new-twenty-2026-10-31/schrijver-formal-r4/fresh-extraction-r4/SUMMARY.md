# MathDB 352827 round 4 partial handback

Incomplete; not accepted. The unconditional theorem mathdb_352827 is absent. Root decides.

RotationCheck.lean proves soundness of a finite bit comparison checker using rotateMask_bit. The 100 Rotation28 modules kernel-check explicit rotation and representative witnesses for every stored index. RotationCoverage28.lean proves indexed_rotation_coverage28 and rotation_coverage28_from_enumeration. The new endpoint mathdb_352827_round4_conditional requires exactly Enumeration27 and Enumeration28; rotation coverage is derived from Enumeration28.

GapRankInverse.lean proves that subtracting the rank from a sequence with gaps at least two gives a strictly increasing sequence bounded by n-k+1, and proves exact reconstruction by adding the rank. These lemmas are not yet connected to the sorted list of an arbitrary literal stable subset. They do not establish enumeration completeness.

Remaining exact Props are the frozen definitions Enumeration27 and Enumeration28 in BridgeTransport.lean. No cardinality argument substitutes for equality. RotationRepresentativeCoverage28 is proved conditionally on Enumeration28, not unconditionally. The gap enumeration completeness and its equality with each stored table remain undone.

Next round: construct the increasing enumeration of a literal stable Finset, prove the consecutive gap bounds from Stable, apply subtractRank_inverse / subtractRank_strict / subtractRank_bound, prove membership in an executable combination enumerator, and kernel-check equality with each stored table. Apply mathdb_352827_round4_conditional to the two resulting enumeration theorems.

All 362 frozen source modules remain byte-identical. frozen-before.json and frozen-after.json record their hashes. Audits check declaration flags, generated companions, attributes and transitive axioms, plus exact equality of the audited module set with the conditional endpoint import closure. Fresh extraction, strict serial builds, leanchecker, negative controls and their resource receipts are reported in results.json. No child agents, git, shared ledger edits, external messages, uploads, network requests or browser tabs were used. Writes were lane-local. Extracting the input archive initially overwrote the lane TASK.txt with the archived round-3 task; it was restored from the binding round-4 text read before extraction. The archived task is preserved in inputs/round3-TASK.txt. Failed development logs are retained.
