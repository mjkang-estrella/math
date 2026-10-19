# Integrity reproduction

From the owned r124 directory, using the independently supplied hashes from the handoff:

    python -B verify.py --root . --finalhash DETACHED_FINAL_SHA256 --reporthash DETACHED_REPORT_SHA256

The verifier uses only this root's packet, REPORT.md, FINAL.json and FINAL-bound programs. It writes nothing, performs no network/subprocess operation, and rejects missing anchors, symlinks, special files, hardlinked payloads, unsafe paths, incorrect exact inventory, wrong source records/blob bytes and mismatched primary/history receipts. It checks the complete canonical tree against a fixed external identity. Its schema is specific to this archive.

Copied controls can be replayed with:

    python -B run_controls.py --root . --finalhash DETACHED_FINAL_SHA256 --reporthash DETACHED_REPORT_SHA256 --output NEW_OWN_OUTPUT_DIRECTORY

The output must be a fresh direct child of the owned root. Tests operate on copies. Some semantic/parser tests use deliberately NEW TEST anchors after resealing the mutant, clearly marked; they do not authenticate a changed mathematical archive. Baseline and ordinary mutations use the original detached anchors. The original tree and each tested input are snapshotted before/after verification. The control receipt itself is outside packet and is not a mathematical gate. Audit denial probes exercise ordinary Python write/process rejection; they are not a hostile-code security sandbox.

There is no frozen target, candidate proof, mathematical test suite, formal support or manuscript to reproduce. Labels in source-register are inventories, and acquisition/hashes do not establish semantic reading. The source/primary/history reading limits are explicit in reading-limits.md.
