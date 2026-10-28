# Gamma-ratio level convexity: complete candidate, credit 0

The full literal Lean endpoint is `GammaLevel.source_convexity : SourceConvexity`.
`SourceLevel` is the genuine positive Gamma ratio, and `SourceConvexity` quantifies
all c>1 and all x>0. The published source instance c=2 is `source_remark16a`.
Uniqueness is certified separately by `existsUnique_sourceLevel`.

Run `python3 verify_candidate.py`. The verifier asserts the absolute Lean binary
hash/version and all pinned package revisions, copies source only to a fresh
temporary directory, compiles all nine modules with warnings as errors, and
audits all 52 public declaration types and axiom closures. No local oleans are
consumed. The full actual outputs are in verification/Checks.log and audit.json.

The written proof and manuscript credit classical perspective convexity, Euler's
product, and Jensen. The preliminary review's assertion that this is not a
perspective sum was corrected by the independent perspective reassessment:
x*F(x,s) is exactly a sum of classical perspectives. No new tool is claimed.
The strongest short/routine objection remains visible in reviews/perspective.

No acceptance or worldwide priority is claimed. One prospective family only;
all levels, helpers and known x>=1 instances earn no separate credit. Independent
final review remains required. No external posting, upload, or MathDB change.
