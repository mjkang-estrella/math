# FT2 focused research round 2

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.
Third-party sources are private and retain their rights.

Read candidate.md for the self-contained report. Full FT2 is unresolved;
count remains 4/10. The supporting all-degree computation and failed symmetric
conversion are in restriction-checkpoint.md. Other exact constraints are in
socle-and-operators-checkpoint.md. Source contracts enumerate actual reading;
primary-comparison.md states contribution limits.

The frozen scope is byte-identical to r14. Inputs include an internal mutable
context snapshot, the complete current brief, private primary reading copies,
and exact references into the fixed r14 history. Large fixed historical trees
are not duplicated. No replay depends on the live campaign ledger or mutable
parent context.

The exact owned input and output lists, sizes and SHA256 are in
input-manifest.json and output-manifest.json. The only metadata files outside
their payload lists are those two manifests and seal.json. Directory membership
must be exactly the ancestors inferred from those files, including no empty
extra directories or symlinks. The fixed r14 tree is authenticated the same way.

After obtaining the DETACHED seal SHA256 from the terminal report, run:

    python -I -B support/verify.py --seal DETACHED_SHA256

The verifier requires the externally supplied anchor. It reads, hashes and
checks only; it does not execute mathematics, old verifiers or third-party code.
It also verifies fifteen historical pinned Git blobs and seven selected
references against the complete pinned catalogue. Inspect and authenticate the
verifier before execution. Its success means INTEGRITY_OK_ONLY, never a
mathematical or contribution acceptance. Passing an incorrect anchor rejects.
No nested agents, external messages, staging, commits, uploads, publication,
submission, manuscript or Lean package are included.
