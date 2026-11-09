# Binomial valuation dependency integrated

2026-10-29 UTC. Root read the completed worker thread, all three proof modules,
the exact endpoint types, the summary, and all57actual root-build type/axiom
reports. The dependency is complete for every m:Nat, including zero:

    binomialOddSum m = sum_(j=0)^m choose(m,j)/(2j+1) in Q
    binomialOddSum_ne_zero m
    padicValRat 2 (binomialOddSum m) = m + padicValNat 2 (m+1).

No summability, moment-vanishing or finite-transform premise remains. The
published supporting theorem is proved internally, not axiomatized. It is
uncredited by itself.

The p-adic proof establishes convergence from factorial norm decay and obtains
M0=0 directly from the positive-index moment recurrence and the bound
norm(M0)<=2^(-j) for every j. The finite binomial transform is proved through
an actual rational-polynomial linear functional and its derivative boundary
identity, rather than assuming the source's hypergeometric transformation.
The tail argument handles j=2 separately and every j>=3 by factorial bounds;
the first term of the normalized final sum is1 and the rest have norm<=1/2.
Rational casts and nonvanishing then yield the literal rational valuation.

Integration copies are formal/BinomialMoments.lean, FiniteTransform.lean,
BinomialOddSum.lean and BinomialAudit.lean. The sole proof-source edits remove
the local import prefix formal.; Audit.lean was renamed BinomialAudit.lean.
Original/integrated hashes and changes are in binomial-import-map.json.
The completed worker's files remain untouched.

Root compiled these copies from source sequentially with the pinned runner,
-j1 -M4096. No candidate prebuilt artifacts were copied. Three module builds
and the exhaustive audit all exited0; module logs are empty; all57declarations
have only propext/Classical.choice/Quot.sound. Root read the actual audit output.
Receipt: formal/binomial-root-replay.json. This root integration replay is
in addition to the implementation worker's fresh isolated component replay.
The Lean audit text matches the worker's byte-for-byte; its log additionally
appends a guard's command/resource JSON line, which the root log omits.
It is not a full Jacobi certificate replay or an independent final review.

Remaining full-target obligations: literal source/logarithm-to-Riccati bridge;
integral midpoint algebra and embedding; binary-weight filtration; normalized
odd primitive and its divisibility; Catalan source top-coefficient identification
and assembly into SourceClaim. Paper, final review and extracted final packet
also remain. Candidate0; accepted32/60 unchanged.
