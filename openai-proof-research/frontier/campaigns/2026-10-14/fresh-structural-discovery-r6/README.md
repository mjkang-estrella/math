# Structural discovery round 6

**UNRESOLVED. Nothing nominated or counted.**

Read `original-scope.md`, then `candidate.md`. The full target is the real
affine-hull theorem for all Barnette graphs. The exact remaining step is
U_C4. The prism and splice proofs and finite obstructions are supporting
technical work, not a substituted result.

All commands use Python 3's standard library; no numerical solver,
third-party Python package, network or Lean installation is needed.
From this directory run:

    python -B verify.py --seal-sha256 EXTERNALLY_RECORDED_SEAL_HASH

The handoff supplies that hash. `seal.sha256` is a convenient local copy,
not a substitute for retaining the external trust anchor. The verifier
checks the seal, both manifest hashes, exact file inventory, every size and
SHA256, and the pinned Git blobs BEFORE executing authenticated code. It
then compares stdout with the original receipts. It never regenerates a
receipt or manifest. Expected final status is
`PASS_INTEGRITY_AND_FINITE_SUPPORT_ONLY_H_UNRESOLVED`.

For optional rejection tests, use:

    python -B mutation_tests.py --seal-sha256 EXTERNALLY_RECORDED_SEAL_HASH

This writes only disposable copies under this owned directory and removes
them afterwards. It modifies source, a receipt, an input and the inventory
on separate copies, and checks rejection before any injected code executes.
The frozen originals remain untouched. Mathematical controls are already
part of `checks.py`.

`exploration-receipt.txt` records 160 seeded probes with possible isomorphic
duplicates. `checks-receipt.txt` records stronger exact supporting checks.
They are not independent reviews and do not prove all-size H.

Original prose CC BY 4.0, original code MIT; Myeongjin Kang, no affiliation.
`inputs/private/` contains third-party and context reading inputs, not
releasable originals. See `RIGHTS.md` and `source-contracts.md` for limits.
No manuscript, formalization, publication or submission is represented.
