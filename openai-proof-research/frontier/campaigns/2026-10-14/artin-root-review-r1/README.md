# Full-R independent review round 1

Read review.md for separate PASS_FULL_R (relative to stipulated premises) and TECHNICAL verdicts. Campaign remains 4/10. No publication authorization.

Run the read-only verifier with an externally supplied detached anchor:

    python -B -I verify.py --seal-sha256 <externally-reported-review-seal>

The verifier authenticates integrity only, including exact frozen source membership, 78 upstream Git identities and the DGM original TeX/archive equality. It executes no child mathematical or third-party code. External frozen sibling packages are required; no standalone portability claim. The original r2 verifier was not replayed against today's mutable ledger. The original package was authenticated with exactly the declared historical ledger bytes. Review replay uses owned context snapshots and never binds whole parent directories or the future live ledger.

Source and output manifests record exact members, sizes and SHA256. seal.json binds their bytes; seal.sha256 is its detached digest, reported externally in the final response.

Myeongjin Kang; no affiliation. Original prose CC BY 4.0/code MIT. Third-party inputs stay private and retain rights.
