# Rights and delivery boundaries

Original public research prose is supplied under the repository's CC BY4.0 convention; original Python code under MIT. Public canonical metadata identifies sources without relicensing their bodies. All files under private/ are source, primary, historical, contextual or search evidence under their original rights and are excluded from public redistribution. Authentication is not a license grant.

Only the exclusively owned r126 directory was written. No shared index, finding, count, acceptance, publication, repository staging/commit/reset or other author's directory was changed. No nested research/review agent or downstream formal/manuscript workflow was started. The public proof is an author candidate requiring separate independent reviews.

Run the verifier with externally supplied values from the detached final report, not values inferred from an untrusted copied packet:

    python -B packet/public/verify.py --root /absolute/path/to/fresh-analytic-discovery-r126 --expected-final FINALHASH --expected-report REPORTHASH

The exact manifest covers all packet files except itself and all packet directories, including empty/hidden entries. FINAL is SHA256 of the exact manifest bytes. REPORT.md is outside the packet, and its SHA256 is separately detached. freeze-anchor.json binds the originally frozen statement and both preceding feasibility notes. The verifier reads only and requires those external anchors. It checks full canonical records/Git blobs, primary pairs, copied history and immutable frozen bytes as well as manifest membership. It is not a mathematical verifier.

Copied controls use the authenticated original verifier against disposable packet copies, remove the copies, and compare the complete original owned directory's preexisting paths/bytes before and afterward. Their receipt is written only after that comparison. They do not mutate an original candidate to test failure behavior. No integrity outcome is a mathematical or contribution gate.
