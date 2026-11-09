# r114 local discovery archive

Read research-report.md, radial-calculation.md, operation-comparison.md and reading-ledger.md. No target was frozen and no nominee or gate is assigned.

Run the read-only integrity verifier with the detached manifest hash reported in FINAL.json outside packet:

    python public/verify.py --packet . --expect-finalhash HASH

The verifier does not infer its trust anchor from the packet. Original bytes are unchanged by verification. Run the separate finite algebra diagnostic with:

    python public/checks.py

Neither operation is a mathematical or contribution gate. Private bodies retain their original rights. FINAL.json and integrity-controls.json are outside packet; controls are run on copies after the final manifest is sealed.
