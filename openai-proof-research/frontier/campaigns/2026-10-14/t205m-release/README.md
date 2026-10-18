# T205M local release preparation

Myeongjin Kang, no affiliation. Preparation only: manuscript review remains pending, no acceptance/count change, archive or publication. Uploads are stopped.

The full unchanged statement concerns every m≥2 and every nonrow, noncolumn partition of N=m(m+1)/2: its complex irreducible multiplicity in the staircase tensor square is at least m−1, sharp at (N−1,1). Pinned upstream inputs are assumed true. The contribution is new to this project; worldwide priority is not established.

`payload-selection.json` is the explicit byte inventory. `verify_preparation.py` checks the known external anchors and selected payloads without interpreting them as verdicts. `release_checks.py` exercises the pending gate and negative controls on disposable copies. `assemble.py` and `verify_bundle.py` derive from T027O and reject a pending independent manuscript anchor even if a caller forges ALL_REVIEW_GATES_PASS.

Parent integration must first adopt the actual independent manuscript verdict and hash in `bundle_common.py`, add an explicitly audited public selection of its report/metadata, and create a separately externally hashed final gate. The expected manuscript verdict spelling is a future schema requirement, not a report of a returned verdict. Assembly must be followed by archive/clean-extraction verification with external hashes and appropriate reproduction checks. No final release verification is claimed here.

Frozen manifests intentionally retain identities for larger research packets. Do not run their whole-packet verifiers against this public subset. Use the release verifier for exact subset membership. See RIGHTS.md, FORMAL-COVERAGE.md and REPRODUCTION.md.
