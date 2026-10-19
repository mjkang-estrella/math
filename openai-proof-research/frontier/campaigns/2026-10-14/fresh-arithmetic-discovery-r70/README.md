# r70: unchanged global cubic target; structured route obstruction

Status: **FULL TARGET UNRESOLVED — NO NOMINATION — COUNT CHANGE ZERO**.

scope.md is a byte-identical copy of the original r69 freeze. The target remains dimension-free unit-weight orthodeco rounding for every fully symmetric real cubic with B<=2I and arbitrary total error, at squared Frobenius cost O(||B-I||F^2+C). No narrowed theorem replaces it.

The completed supporting result is in structured-metric-deflation-obstruction.md. It proves that even an HS-isometric compressed matrix product containing the physical identity, with B<=I and row Gram<=I, can have BOTH residuals increase under the latest prescribed unit-preserving global-maximizer deflation. The example has five cubic coordinates and six physical diagonal coordinates; every global maximizer has the same obstruction. Exact checks use only standard-library rational arithmetic.

attempts-and-unpaid-bridge.md records the best-basis coercivity and CP-map routes, their precise missing interfaces, and the boundary of the failed deflation potential. reading-limits.md and the two receipt files distinguish actual semantic reads from retained provenance. Private source and primary bodies stay under ignored private/; they are excluded from the public manifest.

Run the read-only checker with an independently supplied MANIFEST.json digest:

    python -B verify.py --expected-manifest-sha256 DIGEST

Optionally append --check-private to authenticate the locally retained source/primary bodies against the public receipts. The digest supplied outside this directory is the trust anchor; the local MANIFEST.sha256 is a convenience copy, not an independent trust root. The verifier checks exact public membership, bytes, regular single-link files, lack of symlinks, and agreement of the exact diagnostic output. Integrity checks and finite diagnostics do not prove the frozen target.

This is collaborative author support, not independent review, literature clearance, campaign acceptance or publication. Earlier R023–R040 are treated as paid; no campaign credit is requested.
