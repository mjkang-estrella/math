# Integrity verification

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; code MIT.

The final `seal.json` binds the exact input and output manifests. Their entries
bind exact paths, sizes and SHA256. The controls are those two manifests and
seal.json; no file may be silently added or omitted. The detached SHA256 of
seal.json is reported externally in the final response. The expected seal must
be supplied by the caller, rather than trusted from the package itself.

Read verify.py and authenticate its bytes using the output manifest before
execution. Run from any directory, with the externally reported anchor:

    python -B /absolute/path/to/torsion-free-solutions-r2/verify.py SEAL_SHA256

The verifier is offline and read only, with a Python audit guard rejecting
write/network/process operations after imports. It checks exact owned
membership; input/output hashes; all 39 frozen r13 files and its two historical
references; the external r13 seal and both manifests; both pinned PDF Git
identities against the authenticated complete catalogue; the unchanged scope;
and the explicit unresolved/no-count disposition. It reports source and owned
before/after equality even on a rejected anchor. Run a negative control using
64 zeroes as the anchor. That run must reject while leaving all protected bytes
unchanged.

The verifier is not a mathematical checker. No coset enumeration, numerical
scan, historical proof code, or computer algebra program was used for the
mathematical claims. Normal-form, quotient and ultraproduct arguments are
written proofs to be reviewed by the parent. No independent proof or
contribution gate is self-awarded.

`unchanged-source-receipt.json` records the comparison against the frozen
external baseline after research. Final read-only replays additionally report
that all owned and external bytes stay unchanged during the replay. Mutable
parent context is snapshotted inside inputs/context; future live parent state
and live campaign ledgers are not dependencies.
