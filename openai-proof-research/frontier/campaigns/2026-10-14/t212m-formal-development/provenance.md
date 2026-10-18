# Provenance

Author: Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT. Parent GPT-6 Astra developed the local Lean support and controls as coauthor work, not independent review. This support isolates the deterministic finite-modification ray-tail argument used in the frozen r74 T212M candidate; it does not alter that candidate or any frozen scope.

The build driver and dependency metadata were adapted from ../t205m-formal-v1/, with module identifiers changed to T212M. Mathlib supplies graph-walk decomposition, finite sums, real arithmetic and tactics. Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 are pinned. See validation/receipt.json for the compiler binary hash and all nine dependency revisions. Cached dependency objects form part of the trusted environment.

The r1 attempt failed because of unused-variable warnings in controls; these were repaired. The r2 finite-segment build passed. The r3 build added the derived-avoidance and tail theorem and passed. The r4 build added Mathlib-based loop erasure and the all-walk tail theorem and passed. The r5 build added a nonnegative-weight certificate and an all-walk graph instance and passed. Only successful r5 records are retained here; no failed record is presented as a passing run.
