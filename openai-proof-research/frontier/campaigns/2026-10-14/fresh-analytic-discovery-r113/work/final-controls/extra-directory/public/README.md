# Local research handoff: r113

Read `research-report.md`, then `regenerative-calculation.md`, `operation-comparison.md`, and `reading-ledger.md`.

This is pre-freeze research with no nominee. No mathematical or contribution gate is assigned. All upstream truth is stipulated at the pin documented in status.json; new calculations retain author-level status.

Verify from any working directory:

    python3 -B /absolute/path/to/packet/public/verify.py --packet /absolute/path/to/packet --expect-finalhash EXTERNAL_SHA256

The required EXTERNAL_SHA256 is the detached manifest hash reported outside this packet. The verifier does not infer a trusted anchor from packet contents. It is offline and read-only, does not execute research code, and does not assess mathematical correctness.

`controls.py` only mutates disposable copies in a new caller-specified scratch directory outside the packet. Final-anchor control results and the report digest are in the outside-packet FINAL.json and integrity-controls.json. The private source bodies are local evidence under their original rights and are not publication assets.
