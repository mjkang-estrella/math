# Independent O217 formal review

Verdict **PASS_SCOPED_SUPPORT**, required repairs none. Read review.md for exact mathematical coverage, reproduction and omissions; reading-limits.md records what was actually read. This is not full O217 formalization, acceptance, contribution clearance, or publication.

Authenticate using the review-manifest SHA-256 supplied externally by the reviewer/parent:

    python3 -B verify.py --anchor EXTERNAL_REVIEW_MANIFEST_SHA256

The verifier is read-only and enforces exact file/directory membership. Hash checks authenticate review bytes, not mathematical truth.

Fresh full packet build evidence is in rebuild-copy/independent-build/. The sibling validation/ inside that copy is archived author evidence, not the independent build. Additional independently authored boundary controls and actual CLI wrapper execution are in IndependentControls.lean, NonincidentMutant.lean, run_independent.py and evidence/. The copied author output-manifest describes the original inventory; new copy outputs are sealed by this review's outer manifest.

Reproduction creates outputs: make another isolated copy before running scripts. The copied rebuild uses --cache ../formal/.lake/packages relative to the campaign (supply the absolute cache path when reproducing). run_independent.py similarly requires the disclosed installed Lean path and campaign dependency cache; these local paths are recorded, not a portability claim. No dependency binaries are included in this review.

Original review prose Myeongjin Kang, no affiliation, CC BY 4.0; original code MIT. Copied implementation retains its original licenses. Third-party manuscript bodies remain private in the existing author packet and are not redistributed here. No count/acceptance or upload.
