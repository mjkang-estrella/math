# r138 research handoff

Outcome: a full author-proof nominee for the unchanged fixed-metric harmonic-growth question H from I130/I133. This packet is not an independent correctness or substantial-contribution review, acceptance, formal proof, manuscript, or release.

Read H-SCOPE.md for the frozen statement, AUTHOR-PROOF.md for the proposed full proof, DERIVATION.md for the preserved prefreeze feasibility work, and READING-LIMITS.md for source/history coverage and failures. REPORT.md and FINAL.json are the outside-payload handoff envelopes. The source/primary/original ledgers are explicit metadata. Protected bodies remain private/local under their original rights.

The root seal is made once by seal_packet.py. Existing envelopes make it refuse a rerun. All payload files and directories are bound exactly by MANIFEST.json; the three root envelopes are excluded to avoid circular hashing. Their SHA256 anchors are supplied independently in the final handoff. To verify read-only:

    python -B verify.py --manifest-sha256 <detached MANIFEST hash> --report-sha256 <detached REPORT hash> --final-sha256 <detached FINAL hash>

A copy may be verified with --root <copy-directory>. Anchors must come from the detached handoff, not from a newly calculated untrusted manifest. The verifier neither writes nor executes packet material. copied_controls.py was run once before sealing on copies of three original files; its eight controls and restored baseline are recorded in controls-results.json. Do not rerun acquisition, evidence-recording, fixture creation, or sealing scripts on the sealed packet. Integrity verification makes no mathematical or historical-certification claim.
