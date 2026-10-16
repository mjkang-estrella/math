# Analytic discovery round14: PCW private handoff

Myeongjin Kang; no affiliation. Original prose CC BY4.0; original code MIT.
Third-party rights retained. No public release or submission.

The distinct selected source is family236. `candidate.md` contains a full
proposed proof of the unchanged posterior critical-wave process target,
including uniform path convergence at time0 for every fixed finite vertex
set. Its Gaussian covariance is A_d phi_d(distance) sqrt(min(s,t)). The
old scalar Gaussian perturbation mechanism and old Gaussian waves are
explicitly credited; the proposed operation is increasing-depth path
replacement followed by independent posterior-martingale bracket averaging.
Neither proof correctness nor substantiality has an independent verdict.
No acceptance is self-awarded; the campaign remains4/10.

Read in this order:

1. `original-scope.md` and `freeze-record.json`: full frozen quantifiers.
2. `screening-before-freeze.md`: target choice and concrete unpaid operation.
3. `candidate.md`: self-contained new deductions against the source contracts.
4. `checkpoints.md`: analytic checks and independent-review obligations.
5. `source-contracts.md`, `source-reading.md`, `operation-comparison.md`:
   exact premises, actual reading extents and credited primary antecedents.
6. `status.json`: no independent PASS, count, manuscript or formalization.

`inputs/context/` contains internal snapshots of the mutable campaign ledger,
rules, complete source catalogue, upstream identity and rights. The verifier
never follows a future live ledger. `inputs/pinned/` contains13 authenticated
P source blobs; `inputs/companion/` contains2 comparison-only Q blobs.
`inputs/primary/` contains4 primary PDFs, exact retrieval metadata and their
text extractions; failed cavity-v3 retrieval is recorded separately from the
successful version2. Other inputs are provenance receipts and the in-flight
coordination/history boundary. Historical programs and payloads are not
executed or recopied. All new writes are confined to this directory.

## Integrity boundary and replay

`manifest.json` enumerates every payload file by exact canonical path, role,
byte size and SHA256, and every directory, including empty directories if
any. `seal.json` binds that manifest by size/SHA256 and binds frozen scope.
The two envelope files are the only derived exceptions to payload membership;
there is no self-referential digest. The detached SHA256 of seal.json is
reported **outside this package**, in the final handoff. Never obtain the
trusted anchor merely by hashing an untrusted received seal.

Inspect `verify.py` and `guard.py` before execution. With the detached seal
anchor and an independently checked verifier code hash, run:

    python -B guard.py --verifier-sha256 EXTERNAL_CODE_HASH --anchor EXTERNAL_SEAL_HASH --controls

Alternatively run the inspected `verify.py --anchor EXTERNAL_SEAL_HASH
--controls` using Python-B. The anchor is required; there is no default.
The verifier authenticates seal bytes before any payload parsing, then
manifest bytes, then all payload bytes. Only afterwards does it parse
source/status/context records. It checks all15 pinned Git blobs against
the internal complete catalogue and immutable scope/count metadata.
It rejects path aliases, duplicate paths/keys, symlinks, special files,
bytecode, missing and unlisted files/directories. Controls use in-memory
mutations; they do not modify the package. A wrong external anchor must
reject before payload parsing.

The guard authenticates verifier code before compiling it, denies audited
write/process/network operations and disables bytecode. It is a bounded
Python audit guard, not an operating-system security sandbox. Final before/
after byte comparisons independently check that replay changed no files.
`inputs/unchanged-inputs.json` records fixed source/context observations;
`verification-receipt.json` distinguishes the preliminary-envelope controls
from the final externally reported anchored replay. Integrity does not
certify the mathematics or contribution, and no numerical experiment is
part of this proof.
