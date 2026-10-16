# Fresh structural discovery r14

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.

Start with candidate.md. Frozen FT2 remains UNRESOLVED in full. Its three
checkpoints contain specialization obstructions, the complete finite-window
argument, and a necessary syzygy-growth condition. Source truth is stipulated;
all supporting new deductions are author arguments, not independent reviews.
The campaign remains 4/10. No public or manuscript/formalization action occurred.

Source contracts, screening decisions and precise reading extents are in
source-contracts.md, screening.md and inputs/reading-records.json. Pinned
source identities are in inputs/pinned-records.json; external primary copies
have exact records in inputs/primary-records.json. Authentication is not reading.

Integrity-only replay from THIS directory:

    python -B support/verify.py --seal-sha256 EXTERNALLY_REPORTED_SEAL_SHA256

The seal digest must come from the external final handoff, not an untrusted
local calculation alone. Inspect and authenticate support/verify.py before
running it. The verifier reads only; it does not execute source TeX, historical
programs, converters or mathematical diagnostics, and it does not read live
ledger/context paths. It checks the exact file inventory and hashes, both
manifests, the frozen scope, source Git blobs and internal source receipts.
All downloaded source material is private and keeps third-party rights.

input-manifest.json lists all owned inputs/private copies with sizes/SHA256.
output-manifest.json lists all original payload outputs, including this
verifier. seal.json binds those two manifests, their role totals, source pin,
and frozen scope. These three metadata files complete the exact owned file
membership. The externally reported digest binds seal.json itself. The final
replay output reports counts and total bytes; it is not a mathematical or
contribution judgment. Source-receipt comparisons describe observations made
at packaging time, without binding future mutable source or ledger state.
