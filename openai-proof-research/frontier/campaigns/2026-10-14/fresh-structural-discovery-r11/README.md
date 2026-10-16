# r11 structural research handoff

Author: Myeongjin Kang; no affiliation. See RIGHTS.md.

Read candidate.md for full frozen R, its unpaid operation and the exact
limits of the supporting calculation. Status: UNRESOLVED, not counted,
campaign remains 4/10. No independent proof or contribution PASS.

Verification requires the original sibling r10/r2 trees and fixed external
files recorded in external-inputs.json. Nothing imports or executes their
code. All copied third-party inputs stay private.

Pin the detached seal SHA256 supplied in the external handoff, then run:

    python -I -B verify.py --seal-sha256 EXTERNALLY_PINNED_DIGEST

For authentication before executing even the verifier, independently
check seal.json against that digest, both manifest hashes against the
seal, and verify.py against outputs-manifest.json, using trusted code.
The verifier authenticates every payload before the checker executes,
checks exact membership and pinned blobs, replays one immutable receipt,
and compares whole inventories on success and failure. It regenerates
no fixture, receipt or inventory and writes nothing. --hash-only skips
the mathematical checker without skipping integrity checks.

The initial failed checker and its stderr are preserved. Final checking
uses exact rational arithmetic, not a graph census, a root-closure proof,
an independent review or a Lean certificate. Final verification stdout
is reported outside the sealed tree to avoid changing its manifest.
