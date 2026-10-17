# W5 contribution recovery r2

Review verdict: **TECHNICAL**, at the original complete scope. Read review.md first, then reading-and-comparison.md. This is a separate contribution gate; the independent proof PASS remains intact. No count, public submission or manuscript work is performed here.

Author of original review artifacts: Myeongjin Kang, no affiliation. Original prose CC BY4.0; original code MIT. Files under private/ are third-party metadata/correction evidence, excluded from any public redistribution unless separately licensed and reviewed. External source/primary bodies remain in their original private locations and are referenced by input-hashes.json. The review verifier does not write files or access the network.

The detached SHA256 of manifest.json is supplied in the parent handoff. From this directory:

    python -B verify.py --anchor THE_EXTERNALLY_SUPPLIED_SHA256 --dependencies

The manifest inventories every file except itself and every subdirectory; its externally supplied digest anchors the verifier as well. A separately trusted parent must authenticate that digest. The verifier additionally checks 33 external immutable inputs and optionally reruns the author's source/blob chain. The current mutable campaign ledger and parent dispositions are captured as snapshots, not expected to remain unchanged at their live paths. Exact membership and file-change controls are recorded in verification-controls.json. Identity checks are not a proof, contribution judgment or timestamp authority.

Failed review r1 is preserved unchanged. Its draft TECHNICAL text was consulted transparently; it was not completed or resealed by this worker. This recovery report's decisive additional comparison is the finite-substitution weighted family in review.md, using two separate unit functionals rather than an orthonormal decomposition. Its original full target is never replaced by the auxiliary family.
