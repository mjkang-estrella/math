# Full A.4 remains unresolved — credit 0

Verified the proposed root-paired flagged Jacobi–Trudi formula against Wachs's
actual equation(1.1), Theorem1.3 and proof: shape(n^(2k)), flags2,4,...,4k,
no sign correction. Kumar2023 Theorem4 on root-of-unity factorization uses
complete root orbits and divisible flags; it does not directly cover this
incomplete cube-root alphabet.

New exact route obstruction: for n=4,k=3, one fixed pair-position tableau class
has residue counts426,427,427 and contributes -t^46 to the flagged polynomial.
Hence cancellation confined to those classes cannot prove positivity. It is
not a source counterexample: other classes cancel it; its full pair-content
coefficient is0. The full target is the still-unproved area-wise inequality
N0>=N1, with N1=N2 proved by pair symmetry.

`python check.py` passes within512MiB/45s/threads1. Full proof/refutation absent;
no Lean, nomination or credit. Counts unchanged:3/30 additional,33/60 total.
See discovery.md for proof of the obstruction, exact source comparison and gap;
provenance.json for URLs/hashes/real dates and access limits.
