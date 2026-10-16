# Integrity verification

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.

The final detached SHA256 of `seal.json` is reported in the final response, outside the package. Given that trusted value, inspect/authenticate `verify.py` against the sealed output-manifest entry before execution. Run with Python isolated and bytecode disabled:

    python -I -B verify.py DETACHED_SEAL_SHA256

The verifier is offline and read only. It checks the exact union of input and output membership plus the three control files, sizes/SHA256, fixed scope digest, complete-catalogue condition, both pinned Git blob identities, and exact external historical files. It denies writes, subprocesses and network events, and compares owned/external fingerprints before and after both accepted and rejected verification. It does not regenerate sources, manifests or fixtures. The external historical files must remain available at their project-relative locations; no standalone portability claim is made.

All mutable context, including the campaign ledger and full inherited brief, has owned snapshots. No future live ledger or mutable parent directory is an external dependency. No historical or third-party code runs. There is no finite mathematical diagnostic to replay: the normal-form and exponent calculations are proved in prose. An integrity acceptance or rejection is not a mathematical proof, contribution assessment, independent PASS or campaign acceptance.
