# Integral midpoint component integrated

Root read the completed implementation thread, all four new proof modules,
the actual type/axiom reports for all 186 declarations (132 explicit and 54
compiler-generated auxiliaries), and the source-only replay program. The four
proof modules and MidpointAudit.lean are copied byte-identically into formal/.
The implementation lane remains unchanged. Hashes: midpoint-import-map.json.

A fresh root-owned copy of the source-only replay was run under
verification/midpoint-root-replay/. All eight proof modules and three audit /
environment-inventory checks passed with warnings as errors. The initial
source directory had no local oleans. All 186 new declarations and 54 reused
filtration declarations use only the permitted three axioms; the exhaustive
new declaration inventory also reports all definitions safe. The actual
midpoint, dependency-audit, and inventory output logs reproduce the worker's
byte-for-byte. Root's sampled peak was 2740840 KiB, below the 3 GiB guard.
The Lean binary hash and pinned mathlib revision were verified by the replay.

The integral pair algebra really satisfies w^2=1+x^2. The coefficient
operator is a proved derivation; two separate involutions control parameter
and spectral parity. The concrete finite-prefix construction of h proves
its own recurrence. Integral ideal membership, polynomial parity extraction,
and coefficient divisibility are derived internally. In particular,
h_odd_normalForm_ring and h_odd_extraction_divisible have no assumed recurrence,
normal-form, or divisibility-preservation premise.

Root additionally compiled SourceDefs/SourceChecks and the three binomial
valuation modules in the fresh directory, then checked their joint imports
with MidpointNormalForm in IntegratedChecks.lean. This confirms coexistence
of the integrated components; it is not a proof connecting the source objects
to the midpoint recurrence. All six additional builds passed. The small
integration logs and hashes are in midpoint-combined-imports.json.

Remaining mathematical-formal bridges: odd-unit primitive construction and
midpoint divisibility; parameter-degree bounds; rational Laurent embedding
and coordinate scaling; literal source/logarithm-to-Riccati identification;
Catalan attainment and final SourceClaim assembly. Manuscript, independent
final review and final extracted packet remain. No source-level theorem or
new acceptance is claimed. Candidate credit 0; count 32/60 unchanged.

Original audit and runner logs retain their trailing blank lines to preserve
byte identity. The default git whitespace check flagged only these EOF blanks;
the commit check permits that one cosmetic condition and retains all others.
