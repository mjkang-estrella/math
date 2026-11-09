# Reproduce r6q

Use Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52,
and the read-only mathlib package cache pinned at
 d13f23b723b8a846827a245b89c10fc7d3f11612.

Extract `nut-r6q-source.zip` into a NEW EMPTY directory inside the authorized
write scope. Set `LEAN_BIN` to the absolute Lean executable and `LEAN_PACKAGES`
to the directory whose package children contain `.lake/build/lib/lean`. Run:

```
python3 -I replay.py
```

The driver refuses existing oleans or replay logs. Its sanitized environment
places HOME and TMPDIR inside the extraction. It compiles modules in modules.json
sequentially with `-j1 -DwarningAsError=true`, then runs leanchecker for each.
Every call uses scripts/capped_r6q.py: at most two CPUs, 120 CPU seconds,
140 wall seconds, 5.75 GiB sampled private memory, and MALLOC_ARENA_MAX=2.
Logs and receipts remain in the extraction. AuditR5 covers every inherited local
declaration, and AuditR6_* cover every new declaration including generated ones.
Each audit prints the module, full type, opaque-inclusive value, unsafe/partial/
axiom flags, and transitive axioms; only propext, Classical.choice and Quot.sound
are permitted. Negative controls cover inherited checks plus a wrong shared
semi-edge sign and a forbidden negative tree slot.

To regenerate the new untrusted data and source certificates from the checked
catalogue records, run scripts/generate_r6q.py, scripts/finish_sources_r6q.py,
scripts/split_enumeration_r6q.py, scripts/split_unsigned_r6q.py,
scripts/batch_supports_r6q.py, scripts/local_obstructions_r6q.py, and scripts/prepare_replay_r6q.py, in that order, using python3 -I. No r2
certificate matrix list is read. Every matrix is enumerated directly after the
checked BFS permutation, with the checked parent edges positive. Exact Bareiss
elimination chooses determinant or principal-minor witnesses. Lean independently
checks every claimed scalar value and the exact finite-set equality. The
reconciliation is new-reconciliation.json: 669 unsigned patterns and 9,172 unique
signed matrices (8,208 nonsingular, 964 singular), difference zero from r2.

scripts/build_r6q.py is the resumable sequential DEVELOPMENT driver. It binds
successful receipts to source hashes and uses the read-only inherited oleans
for development only. The fresh extracted replay uses neither those oleans nor
that extra search path and deliberately refuses to resume a nonempty build.

See results.json and SUMMARY.md for the actual achieved validation state. Root
alone adjudicates acceptance; successful replay does not self-accept this lane.
