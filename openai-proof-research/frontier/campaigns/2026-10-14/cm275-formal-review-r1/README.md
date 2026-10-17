# Independent CM275 scoped formal review

Verdict and limits: review.md. Authenticate using `python -B verify.py --anchor EXTERNAL_REVIEW_MANIFEST_SHA256`. The verifier is read-only and checks exact membership and hashes plus the explicitly anchored dependencies. Integrity does not rerun Lean or certify the full theorem.

Fresh author replay: copy the authenticated formal package to a working directory and use its README rebuild command with explicit pinned compiler/cache. The actual independent final replay is retained in final-package-copy/replay-final; this copied package has added logs and is intentionally no longer the author's sealed inventory. Reviewer controls can be replayed in a working copy using run_lean.py after compiling work/CM275.lean, then IndependentControls.lean, AlgebraicControls.lean and IndependentAxioms.lean. The runner writes only inside that working copy. Compiler/cache trust and exact identities are documented separately.

Myeongjin Kang, no affiliation. Original review prose CC BY 4.0; original reviewer code MIT. Copied implementation, manifests and third-party provenance retain their original rights. Third-party inputs are private and are not licensed by this review. This packet is a review artifact, not a public-upload allowlist. No campaign count or publication is authorized by this verdict.
