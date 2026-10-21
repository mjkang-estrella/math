# Read-only verification

Run `python verify.py ROOT --final-sha256 FINAL_SHA256 --manifest-sha256 MANIFEST_SHA256 --report-sha256 REPORT_SHA256`, replacing all three digest arguments with the detached exact anchors in the handoff. ROOT is the absolute path to this r143 directory or an exact byte copy of it. The verifier writes nothing, requires the three external anchors, rejects symlinks and unlisted/missing files, and checks every listed payload size and hash. It does not derive its trust anchors from the same files it checks.

The payload is the whole root except exactly FINAL.md, MANIFEST.json and REPORT.md at root level. Those three outside envelopes are checked using the supplied detached hashes. Nested control-fixture envelopes remain ordinary payload. A copied subset must have its own manifest: the original manifest cannot certify a reduced copy. The included fixture is explicitly a one-file selection of original prose and has separate membership/anchors.

scratch/control-results.json records seven preseal copied integrity controls. Do not rerun scratch/run-controls-r3.py on the sealed root; it refuses after root envelopes exist. No changes to the packet are needed for verification. Hash/inventory checks do not constitute mathematical, contribution or acceptance gates.

Private source/primary/history inputs retain original rights; this is a local discovery evidence packet, not a publication release. See READING-LIMITS-R3.md for semantic-read and isolation limits.
