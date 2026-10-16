# Nodal power T4 independent review r1

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT. Third-party rights retained. Private research material.

Read review.md first. Mathematics: PASS_FULL_T4 with two explicit elementary reviewer repairs; the immutable author proof NEEDS_REVISION. Contribution: TECHNICAL. Nothing is counted; campaign 4/10. The repaired derivation reaches one smooth ordinary metric on S³×S¹ and one fixed positive power, with the whole base-three source transfer in source-transfer.md. This is not approval of the unchanged author text or a publication decision.

repairs.md gives exact corrections and downstream accounting. operation-comparison.md and source-reading.md distinguish bodies actually read from abstracts/listings and compare the operations. original-scope.md is an immutable byte copy. inputs/author is the complete authenticated author package; inputs/context freezes parent and campaign context; inputs/primary retains versioned research inputs.

The detached SHA256 of seal.json is reported externally in the review handoff. Run the inspected verifier with that external digest:

    python -B verify.py --anchor EXTERNAL_REVIEW_SEAL_SHA256

Optionally add --original-author with the absolute frozen author directory to compare its current exact bytes and membership. The verifier authenticates its required external seal before parsing JSON payload, then authenticates the manifest before payload semantics. It rejects unsafe/duplicate paths, JSON duplicate keys, symlinks, file aliases, bytecode, special files and extra or missing files/directories. All pinned Git blob identities are tied to the internal complete catalogue. No live mutable ledger is consulted. Integrity does not prove mathematics or contribution.

verification-controls.json records the positive and wrong-anchor controls under an inspected write/process/network-denying guard; final-audit.json records the exact final counts and expected final replay output, which is compared to the actual sealed replay in the external handoff. Counts in pre-final and final receipts differ by the explicitly added final receipt files. No manifest contains its own digest or the seal digest.
