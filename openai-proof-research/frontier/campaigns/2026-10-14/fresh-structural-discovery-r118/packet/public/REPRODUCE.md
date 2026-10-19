# Read-only verification

From the assigned round directory, run:

    python -B packet/public/verify.py --packet packet --finalhash <detached MANIFEST.json SHA256> --reporthash <detached public/report.md SHA256> --tree ../../../../sources/preprints-tree.json

Supply the two hashes from the outside-packet FINAL-ANCHORS.json or the parent handoff. The verifier will not use an in-packet anchor as a substitute. The tree argument must be the complete 13223-entry truncated=false tree, not sources/tree.json. The verifier does not download anything, execute tests, write files or inspect mathematical truth.

The finite diagnostic is a separate command:

    python -B packet/public/finite_checks.py

Its recorded stdout is public/finite-checks.json. These bounded identities are not theorem or contribution gates. Copied mutation controls are run by the outside-packet run_controls.py; they use temporary copies only within controls/ and retain their result outside the packet. The original sealed packet is never modified by that script.
