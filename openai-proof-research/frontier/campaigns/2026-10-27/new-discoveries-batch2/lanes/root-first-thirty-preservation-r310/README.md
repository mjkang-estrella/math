# Original thirty preservation check

This root orchestration check compares the original campaign ledger with its
recorded immutable SHA256, its thirty accepted records with the second-campaign
context, and each original packet with its recorded digest. It also compares
the thirty stored publication DOI, MathDB paper URL, and problem-ID mappings
against the previously derived accepted-family index.

This verifies preservation of local evidence and recorded links, not current
external URL availability, publication status, novelty, or a new mathematical
audit. It does not alter either campaign ledger or any accepted artifact.

The administrative schemas and a sample index entry were inspected before this
check; the three complete administrative inputs are copied and hash-bound before
their substantive comparison. Proof packets are only hashed, never extracted or
read. No mathematical investigation is undertaken by the root.

Run `check.py build` followed by `check.py verify` in a separate process, both
under the existing campaign helper guard. The manifest excludes only itself and
the final verification receipt. No new credit is claimed.
