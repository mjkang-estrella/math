# Read-only verification

Run python verify.py --root /absolute/path/to/packet --final-sha256 FINAL_ANCHOR --manifest-sha256 MANIFEST_ANCHOR --report-sha256 REPORT_ANCHOR, using all three exact detached SHA256 values from the terminal handoff. The verifier writes nothing and executes no payload, fetcher or historical checker.

It authenticates three envelopes first, validates safe unique manifest paths, rejects symlinks, and checks the exact regular-file set plus sizes/SHA256s. It does not certify modes, hardlink policy, empty directories, incoming publisher signatures, mathematical correctness, contribution or acceptance.

SOURCE-AUTH and PRIMARY-AUTH separately describe original incoming authentication and selected/derived membership. ORIGINAL-AUTH records named old local byte identities after reading, not inherited packet membership. AUTH-RECHECK records the separately performed source/tree, incoming and selected-byte comparisons. Do not run acquisition, scan, authentication, control or seal writers on the sealed real packet.

The copied controls use only a selected copy of original r145 GAPS prose plus a newly enumerated manifest and two fixture envelopes. They never apply a source/original manifest to a reduced copy. The fixture remains private. Each verification invocation is checked for no file-byte modifications. Final independent sha256sum anchors are outside the payload membership.
