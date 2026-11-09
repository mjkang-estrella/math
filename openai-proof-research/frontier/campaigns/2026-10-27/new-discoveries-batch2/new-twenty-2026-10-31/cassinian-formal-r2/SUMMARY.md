Implementation complete; pending root's independent acceptance. Zero credit. Campaign remains 12/20 beyond 39.

The single thin-wedge complement U is proved open, connected, proper, ordinarily star-convex and StrictlyStarlike about 0. Its actual mathlib frontier is proved to be precisely the two wedge rays. Exact inequalities prove that the radius-7/4 Cassinian ball contains 4+i and excludes its midpoint 2+i/2. The ball therefore fails ordinary star-convexity even when the domain meets the stricter finite-boundary visibility hypothesis.

Literal Lean endpoints in formal/Wedge.lean:

- Cassinian331705.Wedge.ordinary_refutation : ¬ Cassinian331705.SourceClaim
- Cassinian331705.Wedge.strict_refutation : ¬ Cassinian331705.SourceClaimStrict

The original Cassinian.lean, including shared definitions, is copied byte for byte. The strict claim strengthens the domain hypothesis to the exact [a,p) finite-frontier condition; both claims conclude ordinary StarConvex of the actual strict Cassinian ball. No implication between the two domain hypotheses is assumed: both are proved for U.

Validation passed: fresh sanitized source-ZIP extraction; strict -j1 -DwarningAsError=true rebuild; leanchecker for Cassinian, Wedge and Sanity; 62-declaration full module-origin audit with full types, bodies, unsafe/partial flags and transitive axioms. Only propext, Classical.choice and Quot.sound occur. All source scans pass. Sanity examples include the original slit failing StrictlyStarlike and the wedge satisfying it. Two negative controls fail with their expected type mismatches. Maximum sampled private RSS was 3,041,329,152 bytes, with a 6 GiB systemd cgroup cap. Actual resource checks confirm CPU affinity {0,1}, CPU limit 120 s and MALLOC_ARENA_MAX=2. Every replay subprocess finished within 14 s.

Read-only input trees have identical before/after hashes. No remaining formal lemma, child agent, git operation, ledger change, external message, browser tab, upload or background job. The optional bounded variant is omitted. Prior-art clearance and the existing independent review's unread-source qualifications are not reassessed; implementation completion is not campaign acceptance or a novelty verdict.

Deliverables: PROOF.md, results.json, pins.json, lean-toolchain, lake-manifest.json, source-manifest.json, 331705-strict-proof-source.zip, scripts/exact.py, scripts/run.py, scripts/replay.py, replay-receipt.json, formal/ sources, fresh extracted/ proof sources and outputs, logs/ receipts, before.json and after.json.

Replay from this lane with an unused extraction-directory name:

    python3 scripts/replay.py extracted-new

The driver refuses to reuse a directory and checks the ZIP's source manifest before compiling. Its pinned cached dependencies are read only; no download is required. Pinned Lean is 4.34.1 and mathlib is d13f23b723b8a846827a245b89c10fc7d3f11612. ZIP SHA256: 02c10af580db8323fa5ed12502b394af44ed1b6a152cdc000cc2d0f541341767.
