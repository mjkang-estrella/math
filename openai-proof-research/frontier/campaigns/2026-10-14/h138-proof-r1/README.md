# H138 first correctness review

Full frozen correctness **PASS** relative to the stipulated pin and operative source proofs. Read REVIEW.md for detailed independent C1–C9 checks and the complete unchanged quantifiers. Contribution **UNREVIEWED**; zero acceptance/count; parent alone integrates and counts.

READING-LIMITS.md records actual reads, initial isolation/search failures, protected rights, truncation recovery, and the limited selected-original authentication boundary. `incoming-membership.json` defines the selective incoming copy; the copied incoming manifest does not certify a reduced copy. Own source/primary/original read ledgers distinguish bytes acquired from proofs read.

The once-only seal binds all payload files and directories. REPORT.md, FINAL.json and MANIFEST.json are outside envelopes. Verify using the three detached hashes returned in the handoff:

    python -B verify.py --manifest-sha256 <MANIFEST hash> --report-sha256 <REPORT hash> --final-sha256 <FINAL hash>

The verifier is read-only. Copied controls were run before sealing and are artifact checks only. Do not rerun acquisition/recording/sealing scripts on a sealed root. All protected incoming bodies, searches and copied fixtures remain private/local under original rights. No upstream or author packet was repaired or resealed.
