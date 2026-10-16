# Focused second attempt on unchanged full LR

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party rights retained privately.

Status: **UNRESOLVED_FULL_LR_AFTER_TWO_ATTEMPTS**. Campaign 4/10 unchanged.
No independent mathematical/contribution PASS, nomination, manuscript, Lean
package, submission or publication.

Read `candidate.md`, then `k4-checkpoint.md` for the realized pair-changing
two-coordinate trade, normal form, extension rigidity and global upper cover.
`design-checkpoint.md` records the exact dual translation and synchronized
inflation's mixed-class upper cover. `source-contracts.md` and
`primary-comparison.md` distinguish actual primary operations from the
remaining full-scope problem. `original-scope.md` is byte-identical to r15.

The single mathematical diagnostic was inspected/authenticated and run once;
`diagnostics/k4-result.json` checks only the displayed F_4 calculation.
The general proofs do not follow from finite testing. Other two-coordinate
gadgets, three-or-more fresh coordinates, nonpencil old labels and arbitrary
linear spaces remain outside the new obstruction.

`manifest.json` specifies exact payload file membership, input/output roles,
sizes/SHA256, and exact directory membership/roles. Metadata are the two
additional files `manifest.json` and `seal.json`. The seal binds the
manifest's size/hash; the SHA256 and size of the seal are reported outside
the package in the handoff. This avoids a circular self-hash. All original
fixed input bytes are preserved or precisely referenced; mutable parent
context is snapshotted internally. `unchanged-source-receipts.json` records
46 fixed external files and a separate observed mutable-ledger interval.
No future live source or ledger bytes are verifier dependencies.
The frozen root-level scope copy is an input; the remaining input files
are under `inputs/`, and authored research/diagnostic files are outputs.

Inspect and authenticate `verify.py` against the verifier hash in the external
handoff before execution. From this directory run:

```sh
python -B verify.py --seal-sha256 EXTERNAL_SHA256_FROM_HANDOFF
```

Do not obtain the anchor by trusting an unanchored file inside the package.
The verifier reads this directory only, checks exact file AND directory
membership/roles, payload sizes/hashes, internal snapshots, three pinned Git
blob identities and historical receipts, and writes nothing. It does not
execute the diagnostic, audit upstream truth, reauthenticate future live
r15 bytes, or decide mathematical/contribution acceptance. Correct anchor
and wrong-anchor rejection were checked under a read-only audit guard.
