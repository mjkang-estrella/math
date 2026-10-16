# Relative CI C, focused second attempt

Myeongjin Kang; no affiliation. Original prose CC BY 4.0, code MIT.
Third-party reading copies and historical inputs remain private with their
original rights. Nothing is authorized for publication or upload here.

Disposition: UNRESOLVED, counted=false, campaign remains 4/10.
Read candidate.md and original-scope.md for the unchanged full target and
exact unpaid comparison. source-contracts.json contains precise provenance
and reading extents. No original r10 code was run or imported.

Verify with an externally supplied seal hash, not an anchor read blindly
from the package itself:

    python -I -B verify.py --anchor EXTERNAL_SHA256

The verifier requires the frozen external r10 package and recorded context
paths under this project. It authenticates exact inventories before replay,
checks all 25 pinned blobs, replays only diagnostics.py under a write/network
denying audit hook, compares the immutable stdout receipt, and confirms
whole inventories unchanged even when replay fails. It does not regenerate
receipts or seal files. Integrity does not imply a mathematical review.
