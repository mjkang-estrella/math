# Root mechanical replay: PASS

The existing Zeckendorf r13 source archive was copied and hash-bound before
inspection, safely extracted into a new root-owned directory, and replayed
serially using the pinned compiler and existing per-invocation limits.

All 24 mathematical modules and the separate supplied audit executable passed.
The audit reports 986 owned declarations across all 24 origins and 20,133
transitive constants, rejecting unsafe/partial declarations and axioms outside
propext, Classical.choice and Quot.sound. All nine package pins match.
The deterministic ZIP rebuild is byte-identical. All 401 original manifest
members were rehashed unchanged. Generated compiler objects were removed from
this root replay directory after success; original lanes were not modified.

This is mechanical root reproduction, not a new independent mathematical review
or source-equivalence adjudication. Execution and output validation reuse the
submitted audit/parser, whose code was inspected before execution. Independent
adversarial source review, novelty/subsumption clearance, manuscript/PDF and
acceptance remain pending. No credit is added; counts remain 9 additional,
39 total, next 40. MathDB delegates retain priority and their existing slots.

See `root-replay-receipt.json`, `owned-audit.json`, `preflight.json`, the 25
`fresh/attempt-*.json` resource receipts and logs, and `FAILURES.md` for the
preserved initial manifest-name setup failure. Final integrity verification is
separate from compilation.
