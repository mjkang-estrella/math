# Arithmetic139 detached artifact report

Discovery disposition: PREFREEZE / no nominee. No frozen theorem, author-proof nomination, independent correctness review, contribution grade, acceptance or count is asserted.

The exact selected payload has 91 regular files and 19407451 bytes. The payload is this run's own selection. private/MANIFEST.json lists every payload path, size and SHA256. FINAL.md, this REPORT.md, the manifest itself and ANCHORS.json are detached envelopes outside that payload, all still inside the exclusive root. ANCHORS.json records the three external SHA256 anchors. The manifest is not inherited or attached to a reduced borrowed packet.

Detached FINAL SHA256: b0fcb66279f7d9940f2241273ac93b4fe8f192885580c90e77c0d9016f1dfc63
Detached MANIFEST SHA256: 2405e688459805a4fa12bae984de34aae1549e9676a30c9bcf99103947c9f08c
The detached REPORT SHA256 is recorded in ANCHORS.json and the handoff; it is intentionally not self-embedded.

Pre-seal artifact checks replayed all16 canonical objects' complete-tree sizes, Git blob identities and SHA256 values, and compared all six authorized completed-original copies byte-for-byte with their exact originals. Those were authentication checks, not semantic rereads or mathematical gates.

private/control-results.json records one clean tiny own copied fixture accepted by the verifier; independently copied tampered, missing-file and extra-file fixtures rejected; and a wrong explicit FINAL anchor rejected. The clean fixture and all source/original bytes remained unchanged. No inherited manifest was used for these fixtures. They are deliberately tiny artifact controls, not theorem tests.

Run the read-only verifier from the actual project root:

    python frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r139/verify_packet.py --root frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r139 --final-sha <external FINAL SHA256> --manifest-sha <external MANIFEST SHA256> --report-sha <external REPORT SHA256>

All three anchors are REQUIRED explicit arguments. The verifier does not trust ANCHORS.json as its anchor source, writes nothing, rejects changed/missing/extra selected files and unsafe paths, and prints artifact MATCH only. The post-seal invocation is reported in the handoff rather than by mutating this sealed report.

The once-only seal is an artifact identity statement. It establishes no mathematical correctness, contribution, formal coverage, exhaustive history clearance, perfect isolation, source rights transfer, publication readiness or campaign count. No public action occurred.
