# H138 first independent contribution review

Read REVIEW.md for the full-scope TECHNICAL assessment and the positive integrated routine derivation. Correctness is UNREVIEWED, conditional on validity of the frozen author proof. GAPS.md separates correctness observations; READING-LIMITS.md and reading-ledger.json record actual reads, search failures/omissions and rights. No acceptance or count is assigned; parent alone integrates.

The exact unchanged theorem is in private/incoming/H-SCOPE.md, with proof and prefreeze derivation copied selectively under explicit input-membership.json. Incoming author metadata has no gate authority. incoming-authentication.json concerns permitted payloads on the actual original root; the reduced copy has no whole-original-root certificate. Source/primary authentication and current selected-original observations are separate.

Original review prose/code are CC BY4.0/MIT. Protected source, primary, history/search/extract and incoming/copy bodies remain private/local under original rights.

seal.py performs one final seal and refuses any existing root envelope. MANIFEST.json binds every payload file and directory exactly; REPORT.md,FINAL.json and MANIFEST.json are outside that payload. Retain the THREE externally returned SHA256 anchors. Read-only replay, after reading verify.py:

    python -B verify.py --manifest-sha256 <detached MANIFEST SHA256> --report-sha256 <detached REPORT SHA256> --final-sha256 <detached FINAL SHA256>

Use --root for an exact copied review packet. Recomputing untrusted anchors is not authentication. The verifier checks bytes only and performs no mathematical gate. controls-results.json records seven preseal copied-fixture cases, including five expected negatives and restored baseline. Do not rerun acquisition, search, evidence capture, copied controls or sealing on this sealed root. Those operations write owned files. Only verify.py is a read-only replay entry point.
