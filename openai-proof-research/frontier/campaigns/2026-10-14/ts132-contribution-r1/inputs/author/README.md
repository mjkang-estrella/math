# TS132 review packet

The full fixed-scope author proof is in candidate.md; original-scope.md is unchanged. Start with those two files, then operation-comparison.md and reading-and-rights.md. The packet is offered for independent proof and contribution reviews, not self-certified.

Run the finite diagnostics without generating bytecode:

    python -B check_local.py

Compare its JSON to local-checks.json. The diagnostics support only the explicitly finite interfaces; the universal theorem is proved analytically in candidate.md.

Read-only exact identity verification:

    python -B verify_packet.py --seal-sha256 EXTERNAL_SHA256_OF_MANIFEST

Use the manifest SHA256 supplied separately by the author/parent, not an internally recomputed value as a substitute for an external anchor. The manifest inventories every payload and directory; it is the only file omitted from its own payload list. Wrong anchors, changed files, extra entries and missing entries must fail. context-receipt.json records bounded historical reading identities but does not require mutable shared ledgers to stay unchanged.

The private directory contains third-party dependency/comparison material. Do not publish this packet wholesale. Rights and exact primary reading limits are documented separately. No source theorem audit, global priority claim, Lean formalization or acceptance count is included.
