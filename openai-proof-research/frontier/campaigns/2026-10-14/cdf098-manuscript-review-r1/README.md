# CDF098 independent manuscript review

Verdict: PASS_MANUSCRIPT, no required repairs, exact full scope unchanged. Read review.md and read-limits.md. This is not a formal PASS, contribution gate, external journal review, acceptance or publication.

Read-only integrity replay in the repository arrangement:

    python -I verify.py --seal-sha256 EXTERNALLY_SUPPLIED_HASH

The verifier authenticates this review, the exact manuscript and frozen mathematical dependencies, source blobs, explicit input receipts and fresh rebuild/visual linkage. It does not execute a compiler, author verifier, Lean, or mathematical program. The external anchor must come from the delivered message, not from a newly computed self-hash. A wrong anchor must be rejected.

Rebuild only an unsealed working copy of rebuild/ using its support/build.py and /tmp/frontier-typeset/tectonic. The compiler must have cached TeX dependencies. Existing visual evidence must not be reused after source or compiler changes without new inspection.

Author: Myeongjin Kang; no affiliation. Original prose CC BY4.0; original code MIT. Third-party inputs remain private and retain their rights. No public action or count change.
