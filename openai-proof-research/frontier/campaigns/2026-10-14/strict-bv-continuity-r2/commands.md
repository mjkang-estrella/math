# Reproduction

From this directory, use the detached root hash given in the handoff:

    python3 -B verify.py --seal-sha256 <SHA256 of seal.json>

For local self-checking against the convenience detached copy:

    python3 -B verify.py

After all authentication succeeds, the verifier replays these commands
without writing bytecode and compares their stdout with the sealed receipts:

    python3 -B checks.py
    python3 -B inputs/private/frozen-r5/verify.py

The verifier generates no evidence or inventory. `check-receipt.json` and
`prior-verifier-receipt.json` were recorded by the author before sealing.
Mutation tests used disposable fixtures and are reported in
`mutation-tests.json`. They did not modify the final package inputs.

No command performs staging, commits, ledger changes, publication,
external messaging, formalization or manuscript generation.
